package main

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"log/slog"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strconv"
	"strings"

	"github.com/google/uuid"
	"github.com/pocketbase/pocketbase"
	"github.com/pocketbase/pocketbase/core"
	"github.com/pocketbase/pocketbase/plugins/migratecmd"

	"github.com/proof-at-home/server/cmd/pocketbase/hooks"
	_ "github.com/proof-at-home/server/cmd/pocketbase/migrations"
	"github.com/proof-at-home/server/src/server/config"
	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/logging"
	"github.com/proof-at-home/server/src/server/static"
	"github.com/proof-at-home/server/src/server/store/gitstore"
)

// getStringSlice extracts a []string from a PocketBase JSONField value.
// PocketBase returns JSONRaw ([]byte) for JSON fields, not []any.
func getStringSlice(record *core.Record, field string) []string {
	raw := record.Get(field)
	if raw == nil {
		return nil
	}
	// Try []any first (in case PocketBase returns parsed values in some contexts)
	if list, ok := raw.([]any); ok {
		var out []string
		for _, v := range list {
			if s, ok := v.(string); ok {
				out = append(out, s)
			}
		}
		return out
	}
	// Handle JSONRaw / []byte / string (the common case for JSONField)
	var b []byte
	switch v := raw.(type) {
	case []byte:
		b = v
	case string:
		b = []byte(v)
	default:
		// Try JSON marshalling as fallback
		var err error
		b, err = json.Marshal(raw)
		if err != nil {
			return nil
		}
	}
	var out []string
	if json.Unmarshal(b, &out) == nil {
		return out
	}
	return nil
}

var (
	gs    *gitstore.GitStore
	forge gitstore.ForgeClient
)

// exportNotesToGit collects all notes from PocketBase and exports them to the
// git "notes" branch. Safe to call from any goroutine (GitStore is mutex-protected).
func exportNotesToGit(app core.App) {
	records, err := app.FindAllRecords("notes")
	if err != nil {
		slog.Error("notes git export: failed to query notes", "error", err)
		return
	}
	if len(records) == 0 {
		return
	}
	notes := make([]data.Note, 0, len(records))
	for _, r := range records {
		notes = append(notes, data.Note{
			NoteID:         r.GetString("note_id"),
			LessonID:       r.GetString("lesson_id"),
			ContentHash:    r.GetString("content_hash"),
			AnchorText:     r.GetString("anchor_text"),
			LineStart:      int(r.GetFloat("line_start")),
			LineEnd:        int(r.GetFloat("line_end")),
			Content:        r.GetString("content"),
			HighlightColor: r.GetString("highlight_color"),
			UserID:         r.GetString("user_id"),
			Username:       r.GetString("username"),
			Status:         r.GetString("status"),
			CreatedAt:      r.GetString("created"),
			UpdatedAt:      r.GetString("updated"),
		})
	}
	if err := gs.ExportNotesToGit(notes); err != nil {
		slog.Error("notes git export failed", "error", err)
	} else {
		slog.Info("notes git export complete", "count", len(notes))
	}
}

func main() {
	cfg := config.Load()
	logging.Init(cfg.LogLevel)

	// Initialize forge client (same logic as src/server/main.go)
	switch cfg.GitForgeType {
	case "local":
		forge = gitstore.NewLocalForge(cfg.GitDataRepoPath)
		slog.Info("Using local forge (auto-merge, no remote)")
	case "gitlab":
		forge = gitstore.NewGitLabForge(
			cfg.GitForgeToken,
			cfg.GitForgeProject,
			cfg.GitForgeAPIURL,
			cfg.WebhookSecret,
			cfg.GitLabProjectPath,
		)
		slog.Info("Using GitLab forge", "project", cfg.GitForgeProject)
	default: // "github"
		forge = gitstore.NewGitHubForge(
			cfg.GitForgeToken,
			cfg.GitForgeProject,
			cfg.GitForgeAPIURL,
			cfg.WebhookSecret,
		)
		slog.Info("Using GitHub forge", "project", cfg.GitForgeProject)
	}

	// Clone/pull data repo and initialize GitStore
	var err error
	gs, err = gitstore.New(cfg.GitDataRepoURL, cfg.GitDataRepoPath, cfg.GitForgeToken, forge)
	if err != nil {
		slog.Error("Failed to initialize git store", "error", err)
		os.Exit(1)
	}

	app := pocketbase.New()

	// Export notes after each webhook-triggered rebuild and after note CRUD.
	gs.SetPostRebuildFn(func() { exportNotesToGit(app) })

	// Set app name on first serve
	app.OnServe().BindFunc(func(se *core.ServeEvent) error {
		settings := app.Settings()
		if settings.Meta.AppName == "Acme" {
			settings.Meta.AppName = "Proof@Home"
			settings.Meta.AppURL = "https://pah.fly.dev"
			if err := app.Save(settings); err != nil {
				slog.Warn("Failed to update app settings", "error", err)
			}
		}
		return se.Next()
	})

	// Register migration system
	migratecmd.MustRegister(app, app.RootCmd, migratecmd.Config{
		Dir:         "cmd/pocketbase/migrations",
		Automigrate: true,
	})

	// Register business logic hooks
	hooks.Register(app)

	// Register custom API routes
	app.OnServe().BindFunc(func(se *core.ServeEvent) error {
		registerRoutes(se, app, cfg)
		return se.Next()
	})

	// Rebuild PocketBase from git on startup
	app.OnServe().BindFunc(func(se *core.ServeEvent) error {
		slog.Info("Rebuilding PocketBase from git data on startup")
		if err := rebuildFromGit(app); err != nil {
			slog.Error("Failed to rebuild from git on startup", "error", err)
		}

		// Wire up rebuild callback so cache is refreshed after each local merge
		if cfg.GitForgeType == "local" {
			gs.SetRebuildFn(func(repoPath string) error {
				return rebuildFromGit(app)
			})
		}

		return se.Next()
	})

	if err := app.Start(); err != nil {
		log.Fatal(err)
	}
}

// registerRoutes adds custom routes that preserve backward compatibility
// with the existing Proof@Home client.
func registerRoutes(se *core.ServeEvent, app core.App, cfg *config.Config) {
	// ── Read routes (PocketBase as cache) ──

	// GET /health
	se.Router.GET("/health", func(e *core.RequestEvent) error {
		return e.JSON(http.StatusOK, map[string]string{"status": "ok"})
	})

	// Installer script redirect
	se.Router.GET("/install.sh", func(e *core.RequestEvent) error {
		return e.Redirect(http.StatusFound, "https://raw.githubusercontent.com/pah-org/proof-at-home/main/scripts/install.sh")
	})

	// GET /conjectures — list all conjectures
	se.Router.GET("/conjectures", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("conjectures")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type conjectureSummary struct {
			ID         string `json:"id"`
			Title      string `json:"title"`
			Difficulty string `json:"difficulty"`
			Prover     string `json:"prover"`
			Status     string `json:"status"`
		}

		summaries := make([]conjectureSummary, 0, len(records))
		for _, r := range records {
			summaries = append(summaries, conjectureSummary{
				ID:         r.GetString("conjecture_id"),
				Title:      r.GetString("title"),
				Difficulty: r.GetString("difficulty"),
				Prover:     r.GetString("prover"),
				Status:     r.GetString("status"),
			})
		}
		return e.JSON(http.StatusOK, summaries)
	})

	// GET /conjectures/{id} — get specific conjecture
	se.Router.GET("/conjectures/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		record, err := app.FindFirstRecordByFilter("conjectures", "conjecture_id = {:pid}", map[string]any{
			"pid": id,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		conjecture := map[string]any{
			"id":              record.GetString("conjecture_id"),
			"title":           record.GetString("title"),
			"difficulty":      record.GetString("difficulty"),
			"prover":          record.GetString("prover"),
			"status":          record.GetString("status"),
			"preamble":        record.GetString("preamble"),
			"lemma_statement": record.GetString("lemma_statement"),
			"hints":           record.Get("hints"),
			"skeleton":        record.GetString("skeleton"),
			"dependencies":    record.Get("dependencies"),
		}
		return e.JSON(http.StatusOK, conjecture)
	})

	// GET /strategies — list strategies
	se.Router.GET("/strategies", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("strategies")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type strategyEntry struct {
			Name        string `json:"name"`
			Kind        string `json:"kind"`
			Prover      string `json:"prover"`
			Description string `json:"description"`
			Priority    int    `json:"priority"`
			Body        string `json:"body"`
		}

		entries := make([]strategyEntry, 0, len(records))
		for _, r := range records {
			entries = append(entries, strategyEntry{
				Name:        r.GetString("name"),
				Kind:        r.GetString("kind"),
				Prover:      r.GetString("prover"),
				Description: r.GetString("description"),
				Priority:    int(r.GetFloat("priority")),
				Body:        r.GetString("body"),
			})
		}

		// Filter by kind if query param provided
		kind := e.Request.URL.Query().Get("kind")
		if kind != "" {
			filtered := make([]strategyEntry, 0)
			for _, s := range entries {
				if s.Kind == kind {
					filtered = append(filtered, s)
				}
			}
			entries = filtered
		}

		return e.JSON(http.StatusOK, entries)
	})

	// GET /strategies/{name} — get specific strategy
	se.Router.GET("/strategies/{name}", func(e *core.RequestEvent) error {
		name := e.Request.PathValue("name")
		record, err := app.FindFirstRecordByFilter("strategies", "name = {:name}", map[string]any{
			"name": name,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		result := map[string]any{
			"name":        record.GetString("name"),
			"kind":        record.GetString("kind"),
			"prover":      record.GetString("prover"),
			"description": record.GetString("description"),
			"priority":    int(record.GetFloat("priority")),
			"body":        record.GetString("body"),
		}
		return e.JSON(http.StatusOK, result)
	})

	// GET /contributions — list contributions
	se.Router.GET("/contributions", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("contributions")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type contributionEntry struct {
			ContributionID       string   `json:"contribution_id"`
			Username             string   `json:"username"`
			ConjecturesAttempted int      `json:"conjectures_attempted"`
			ConjecturesProved    int      `json:"conjectures_proved"`
			TotalCostUSD         float64  `json:"total_cost_usd"`
			ArchiveSHA256        string   `json:"archive_sha256"`
			Prover               string   `json:"prover"`
			ConjectureIDs        []string `json:"conjecture_ids,omitempty"`
			ProofStatus          string   `json:"proof_status,omitempty"`
			CertifiedBy          []string `json:"certified_by,omitempty"`
			NFTMetadata          any      `json:"nft_metadata"`
		}

		entries := make([]contributionEntry, 0, len(records))
		for _, r := range records {
			entries = append(entries, contributionEntry{
				ContributionID:       r.GetString("contribution_id"),
				Username:             r.GetString("username"),
				ConjecturesAttempted: int(r.GetFloat("conjectures_attempted")),
				ConjecturesProved:    int(r.GetFloat("conjectures_proved")),
				TotalCostUSD:         r.GetFloat("cost_usd"),
				ArchiveSHA256:        r.GetString("archive_sha256"),
				Prover:               r.GetString("prover"),
				ConjectureIDs:        getStringSlice(r, "conjecture_ids"),
				ProofStatus:          r.GetString("proof_status"),
				CertifiedBy:          getStringSlice(r, "certified_by"),
				NFTMetadata:          r.Get("nft_metadata"),
			})
		}
		return e.JSON(http.StatusOK, entries)
	})

	// GET /contributions/{id} — get specific contribution
	se.Router.GET("/contributions/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		record, err := app.FindFirstRecordByFilter("contributions", "contribution_id = {:cid}", map[string]any{
			"cid": id,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		result := map[string]any{
			"contribution_id":       record.GetString("contribution_id"),
			"username":              record.GetString("username"),
			"conjectures_attempted": int(record.GetFloat("conjectures_attempted")),
			"conjectures_proved":    int(record.GetFloat("conjectures_proved")),
			"total_cost_usd":        record.GetFloat("cost_usd"),
			"archive_sha256":        record.GetString("archive_sha256"),
			"prover":                record.GetString("prover"),
			"conjecture_ids":        getStringSlice(record, "conjecture_ids"),
			"proof_status":          record.GetString("proof_status"),
			"certified_by":          getStringSlice(record, "certified_by"),
			"nft_metadata":          record.Get("nft_metadata"),
		}
		return e.JSON(http.StatusOK, result)
	})

	// GET /contributions/{id}/proofs — list proofs for a contribution
	se.Router.GET("/contributions/{id}/proofs", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		records, err := app.FindAllRecords("proofs")
		if err != nil {
			return e.JSON(http.StatusOK, []any{})
		}

		type proofEntry struct {
			ContributionID string  `json:"contribution_id"`
			ConjectureID   string  `json:"conjecture_id"`
			Username       string  `json:"username"`
			Success        bool    `json:"success"`
			ProofScript    string  `json:"proof_script"`
			CostUSD        float64 `json:"cost_usd"`
			Attempts       int     `json:"attempts"`
			ErrorOutput    string  `json:"error_output"`
		}

		var proofs []proofEntry
		for _, r := range records {
			if r.GetString("contribution_id") != id {
				continue
			}
			proofs = append(proofs, proofEntry{
				ContributionID: r.GetString("contribution_id"),
				ConjectureID:   r.GetString("conjecture_id"),
				Username:       r.GetString("username"),
				Success:        r.GetBool("success"),
				ProofScript:    r.GetString("proof_script"),
				CostUSD:        r.GetFloat("cost_usd"),
				Attempts:       int(r.GetFloat("attempts")),
				ErrorOutput:    r.GetString("error_output"),
			})
		}
		if proofs == nil {
			proofs = []proofEntry{}
		}
		return e.JSON(http.StatusOK, proofs)
	})

	// GET /certificates — list certificates
	se.Router.GET("/certificates", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("certificates")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type certificateEntry struct {
			CertificateID       string `json:"certificate_id"`
			CertifierUsername   string `json:"certifier_username"`
			PackagesCertified   int    `json:"packages_certified"`
			ConjecturesCompared int    `json:"conjectures_compared"`
			Recommendation      string `json:"recommendation"`
			NFTMetadata         any    `json:"nft_metadata"`
		}

		entries := make([]certificateEntry, 0, len(records))
		for _, r := range records {
			entries = append(entries, certificateEntry{
				CertificateID:       r.GetString("certificate_id"),
				CertifierUsername:   r.GetString("certifier_username"),
				PackagesCertified:   int(r.GetFloat("packages_certified")),
				ConjecturesCompared: int(r.GetFloat("conjectures_compared")),
				Recommendation:      r.GetString("recommendation"),
				NFTMetadata:         r.Get("nft_metadata"),
			})
		}
		return e.JSON(http.StatusOK, entries)
	})

	// GET /contribution-reviews — list certificate packages
	se.Router.GET("/contribution-reviews", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("contributions")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type certPkg struct {
			ContributorContributionID string   `json:"contributor_contribution_id"`
			ContributorUsername       string   `json:"contributor_username"`
			Prover                    string   `json:"prover"`
			ConjectureIDs             []string `json:"conjecture_ids"`
			ArchiveURL                string   `json:"archive_url"`
			ArchiveSHA256             string   `json:"archive_sha256"`
			ProofStatus               string   `json:"proof_status,omitempty"`
			CertifiedBy               []string `json:"certified_by,omitempty"`
		}

		packages := make([]certPkg, 0, len(records))
		for _, r := range records {
			contributionID := r.GetString("contribution_id")

			prover := r.GetString("prover")
			if prover == "" {
				prover = "rocq"
			}

			packages = append(packages, certPkg{
				ContributorContributionID: contributionID,
				ContributorUsername:       r.GetString("username"),
				Prover:                    prover,
				ConjectureIDs:             getStringSlice(r, "conjecture_ids"),
				ArchiveURL:                "/contributions/" + contributionID + "/archive",
				ArchiveSHA256:             r.GetString("archive_sha256"),
				ProofStatus:               r.GetString("proof_status"),
				CertifiedBy:               getStringSlice(r, "certified_by"),
			})
		}
		return e.JSON(http.StatusOK, packages)
	})

	// GET /contributions/{contributionID}/archive — stream tar.gz from git proofs dir
	se.Router.GET("/contributions/{contributionID}/archive", func(e *core.RequestEvent) error {
		contributionID := e.Request.PathValue("contributionID")

		proofsDir := filepath.Join(gs.RepoPath(), "contributions", contributionID, "proofs")
		if _, err := os.Stat(proofsDir); os.IsNotExist(err) {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "archive not found"})
		}

		e.Response.Header().Set("Content-Type", "application/gzip")
		e.Response.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=%s-proofs.tar.gz", contributionID))

		gw := gzip.NewWriter(e.Response)
		defer gw.Close()
		tw := tar.NewWriter(gw)
		defer tw.Close()

		entries, err := os.ReadDir(proofsDir)
		if err != nil {
			slog.Error("Failed to read proofs dir", "error", err, "path", proofsDir)
			return nil
		}

		for _, entry := range entries {
			if entry.IsDir() {
				continue
			}
			filePath := filepath.Join(proofsDir, entry.Name())
			info, err := entry.Info()
			if err != nil {
				continue
			}
			header, err := tar.FileInfoHeader(info, "")
			if err != nil {
				continue
			}
			header.Name = entry.Name()
			if err := tw.WriteHeader(header); err != nil {
				slog.Error("Failed to write tar header", "error", err)
				return nil
			}
			f, err := os.Open(filePath)
			if err != nil {
				continue
			}
			io.Copy(tw, f)
			f.Close()
		}
		return nil
	})

	// ── Write routes (git-backed via GitStore) ──

	// POST /contributions — create contribution via GitStore
	se.Router.POST("/contributions", func(e *core.RequestEvent) error {
		var summary data.Contribution
		if err := json.NewDecoder(e.Request.Body).Decode(&summary); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		if err := gs.AddContribution(summary); err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to create contribution: " + err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{"status": "accepted"})
	})

	// POST /contributions/batch — submit contribution summary via GitStore
	se.Router.POST("/contributions/batch", func(e *core.RequestEvent) error {
		var summary data.Contribution
		if err := json.NewDecoder(e.Request.Body).Decode(&summary); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		if err := gs.AddContribution(summary); err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to create contribution: " + err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{"status": "accepted"})
	})

	// POST /contributions/{id}/proofs — submit proof via GitStore
	se.Router.POST("/contributions/{id}/proofs", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")

		var proof data.Proof
		if err := json.NewDecoder(e.Request.Body).Decode(&proof); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		proof.ContributionID = id
		if err := gs.AddProof(proof); err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to add proof: " + err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{"status": "accepted"})
	})

	// PATCH /contributions/{id} — finalize contribution, return commit SHA
	se.Router.PATCH("/contributions/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")

		var summary data.Contribution
		if err := json.NewDecoder(e.Request.Body).Decode(&summary); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		summary.ContributionID = id
		commitSHA, err := gs.FinalizeContribution(id, summary)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to finalize: " + err.Error()})
		}

		return e.JSON(http.StatusOK, map[string]string{
			"commit_sha": commitSHA,
			"status":     "pending",
		})
	})

	// POST /contributions/{id}/seal — seal contribution, create PR
	se.Router.POST("/contributions/{id}/seal", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")

		var nftMetadata any
		if err := json.NewDecoder(e.Request.Body).Decode(&nftMetadata); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		prURL, err := gs.SealContribution(id, nftMetadata)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to seal: " + err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{
			"pr_url": prURL,
			"status": "pending",
		})
	})

	// POST /certificates — submit certificate via GitStore
	se.Router.POST("/certificates", func(e *core.RequestEvent) error {
		var certificate data.Certificate
		if err := json.NewDecoder(e.Request.Body).Decode(&certificate); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		commitSHA, err := gs.AddCertificate(certificate)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to create certificate: " + err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{
			"commit_sha": commitSHA,
			"status":     "accepted",
		})
	})

	// POST /certificates/{id}/seal — seal certificate, create PR
	se.Router.POST("/certificates/{id}/seal", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")

		var nftMetadata any
		if err := json.NewDecoder(e.Request.Body).Decode(&nftMetadata); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		prURL, err := gs.SealCertificate(id, nftMetadata)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to seal: " + err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{
			"pr_url": prURL,
			"status": "pending",
		})
	})

	// GET /expositions — list expositions
	se.Router.GET("/expositions", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("expositions")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type expositionEntry struct {
			ExpositionID   string  `json:"exposition_id"`
			AuthorUsername string  `json:"author_username"`
			ContributionID string  `json:"contribution_id,omitempty"`
			ConjectureID   string  `json:"conjecture_id,omitempty"`
			Prover         string  `json:"prover,omitempty"`
			ExpositionText string  `json:"exposition_text"`
			CostUSD        float64 `json:"cost_usd"`
			StrategyUsed   string  `json:"strategy_used,omitempty"`
			NFTMetadata    any     `json:"nft_metadata"`
			Domain         string  `json:"domain,omitempty"`
			Title          string  `json:"title,omitempty"`
			Summary        string  `json:"summary,omitempty"`
		}

		entries := make([]expositionEntry, 0, len(records))
		for _, r := range records {
			entries = append(entries, expositionEntry{
				ExpositionID:   r.GetString("exposition_id"),
				AuthorUsername: r.GetString("author_username"),
				ContributionID: r.GetString("contribution_id"),
				ConjectureID:   r.GetString("conjecture_id"),
				Prover:         r.GetString("prover"),
				ExpositionText: r.GetString("exposition_text"),
				CostUSD:        r.GetFloat("cost_usd"),
				StrategyUsed:   r.GetString("strategy_used"),
				NFTMetadata:    r.Get("nft_metadata"),
				Domain:         r.GetString("domain"),
				Title:          r.GetString("title"),
				Summary:        r.GetString("summary"),
			})
		}
		return e.JSON(http.StatusOK, entries)
	})

	// GET /expositions/{id} — get specific exposition
	se.Router.GET("/expositions/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		record, err := app.FindFirstRecordByFilter("expositions", "exposition_id = {:eid}", map[string]any{
			"eid": id,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		result := map[string]any{
			"exposition_id":   record.GetString("exposition_id"),
			"author_username": record.GetString("author_username"),
			"contribution_id": record.GetString("contribution_id"),
			"conjecture_id":   record.GetString("conjecture_id"),
			"prover":          record.GetString("prover"),
			"proof_script":    record.GetString("proof_script"),
			"exposition_text": record.GetString("exposition_text"),
			"cost_usd":        record.GetFloat("cost_usd"),
			"strategy_used":   record.GetString("strategy_used"),
			"nft_metadata":    record.Get("nft_metadata"),
			"domain":          record.GetString("domain"),
			"title":           record.GetString("title"),
			"summary":         record.GetString("summary"),
		}
		return e.JSON(http.StatusOK, result)
	})

	// POST /expositions — submit exposition via GitStore
	se.Router.POST("/expositions", func(e *core.RequestEvent) error {
		var expo data.Exposition
		if err := json.NewDecoder(e.Request.Body).Decode(&expo); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		commitSHA, err := gs.AddExposition(expo)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to create exposition: " + err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{
			"commit_sha": commitSHA,
			"status":     "accepted",
		})
	})

	// POST /expositions/{id}/seal — seal exposition, create PR
	se.Router.POST("/expositions/{id}/seal", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")

		var nftMetadata any
		if err := json.NewDecoder(e.Request.Body).Decode(&nftMetadata); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		prURL, err := gs.SealExposition(id, nftMetadata)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to seal: " + err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{
			"pr_url": prURL,
			"status": "pending",
		})
	})

	// ── Lesson routes ──

	// GET /lessons — list lessons
	se.Router.GET("/lessons", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("lessons")
		if err != nil {
			return e.JSON(http.StatusOK, []any{})
		}

		type lessonEntry struct {
			LessonID       string   `json:"lesson_id"`
			AuthorUsername string   `json:"author_username"`
			Title          string   `json:"title"`
			Topic          string   `json:"topic"`
			Difficulty     string   `json:"difficulty"`
			Description    string   `json:"description"`
			ConjectureIDs  []string `json:"conjecture_ids"`
			Published      bool     `json:"published"`
		}

		entries := make([]lessonEntry, 0, len(records))
		for _, r := range records {
			entries = append(entries, lessonEntry{
				LessonID:       r.GetString("lesson_id"),
				AuthorUsername: r.GetString("author_username"),
				Title:          r.GetString("title"),
				Topic:          r.GetString("topic"),
				Difficulty:     r.GetString("difficulty"),
				Description:    r.GetString("description"),
				ConjectureIDs:  getStringSlice(r, "conjecture_ids"),
				Published:      r.GetBool("published"),
			})
		}
		return e.JSON(http.StatusOK, entries)
	})

	// GET /lessons/{id} — get specific lesson
	se.Router.GET("/lessons/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		record, err := app.FindFirstRecordByFilter("lessons", "lesson_id = {:lid}", map[string]any{
			"lid": id,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		result := map[string]any{
			"lesson_id":       record.GetString("lesson_id"),
			"author_username": record.GetString("author_username"),
			"title":           record.GetString("title"),
			"topic":           record.GetString("topic"),
			"difficulty":      record.GetString("difficulty"),
			"description":     record.GetString("description"),
			"prerequisites":   record.GetString("prerequisites"),
			"conjecture_ids":  getStringSlice(record, "conjecture_ids"),
			"published":       record.GetBool("published"),
			"content":         record.GetString("content"),
			"ai_annotations":  record.Get("ai_annotations"),
		}
		return e.JSON(http.StatusOK, result)
	})

	// POST /lessons — create lesson via GitStore
	se.Router.POST("/lessons", func(e *core.RequestEvent) error {
		var lesson data.Lesson
		if err := json.NewDecoder(e.Request.Body).Decode(&lesson); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON: " + err.Error()})
		}
		if lesson.LessonID == "" {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "lesson_id is required"})
		}

		sha, err := gs.AddLesson(lesson)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusOK, map[string]string{
			"status":     "created",
			"commit_sha": sha,
		})
	})

	// PATCH /lessons/{id} — update lesson via GitStore
	se.Router.PATCH("/lessons/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		var lesson data.Lesson
		if err := json.NewDecoder(e.Request.Body).Decode(&lesson); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON: " + err.Error()})
		}
		lesson.LessonID = id

		sha, err := gs.UpdateLesson(id, lesson)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusOK, map[string]string{
			"status":     "updated",
			"commit_sha": sha,
		})
	})

	// ── Notes routes ──

	// helper to convert a PocketBase notes record to the API response shape
	noteRecordToMap := func(r *core.Record) map[string]any {
		return map[string]any{
			"note_id":         r.GetString("note_id"),
			"lesson_id":       r.GetString("lesson_id"),
			"content_hash":    r.GetString("content_hash"),
			"anchor_text":     r.GetString("anchor_text"),
			"line_start":      int(r.GetFloat("line_start")),
			"line_end":        int(r.GetFloat("line_end")),
			"content":         r.GetString("content"),
			"highlight_color": r.GetString("highlight_color"),
			"user_id":         r.GetString("user_id"),
			"username":        r.GetString("username"),
			"status":          r.GetString("status"),
			"created_at":      r.GetString("created"),
			"updated_at":      r.GetString("updated"),
		}
	}

	// GET /lessons/{id}/notes — list notes for a lesson
	se.Router.GET("/lessons/{id}/notes", func(e *core.RequestEvent) error {
		lessonID := e.Request.PathValue("id")
		records, err := app.FindRecordsByFilter("notes", "lesson_id = {:lid}", "line_start", -1, 0, map[string]any{
			"lid": lessonID,
		})
		if err != nil {
			return e.JSON(http.StatusOK, []any{})
		}
		result := make([]map[string]any, 0, len(records))
		for _, r := range records {
			result = append(result, noteRecordToMap(r))
		}
		return e.JSON(http.StatusOK, result)
	})

	// POST /lessons/{id}/notes — create a note
	se.Router.POST("/lessons/{id}/notes", func(e *core.RequestEvent) error {
		lessonID := e.Request.PathValue("id")

		var body struct {
			NoteID         string `json:"note_id"`
			ContentHash    string `json:"content_hash"`
			AnchorText     string `json:"anchor_text"`
			LineStart      int    `json:"line_start"`
			LineEnd        int    `json:"line_end"`
			Content        string `json:"content"`
			HighlightColor string `json:"highlight_color"`
			UserID         string `json:"user_id"`
			Username       string `json:"username"`
			Status         string `json:"status"`
		}
		if err := json.NewDecoder(e.Request.Body).Decode(&body); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		if body.NoteID == "" {
			body.NoteID = uuid.New().String()
		}
		if body.Status == "" {
			body.Status = "active"
		}

		if e.Auth != nil {
			body.UserID = e.Auth.Id
			if name := e.Auth.GetString("name"); name != "" {
				body.Username = name
			} else if e.Auth.Email() != "" {
				body.Username = e.Auth.Email()
			}
		}

		col, err := app.FindCollectionByNameOrId("notes")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "notes collection not found"})
		}
		record := core.NewRecord(col)
		record.Set("note_id", body.NoteID)
		record.Set("lesson_id", lessonID)
		record.Set("content_hash", body.ContentHash)
		record.Set("anchor_text", body.AnchorText)
		record.Set("line_start", body.LineStart)
		record.Set("line_end", body.LineEnd)
		record.Set("content", body.Content)
		record.Set("highlight_color", body.HighlightColor)
		record.Set("user_id", body.UserID)
		record.Set("username", body.Username)
		record.Set("status", body.Status)

		if err := app.Save(record); err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to create note: " + err.Error()})
		}

		go exportNotesToGit(app)
		return e.JSON(http.StatusCreated, noteRecordToMap(record))
	})

	// PATCH /notes/{noteId} — update a note
	se.Router.PATCH("/notes/{noteId}", func(e *core.RequestEvent) error {
		noteID := e.Request.PathValue("noteId")
		record, err := app.FindFirstRecordByFilter("notes", "note_id = {:nid}", map[string]any{
			"nid": noteID,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		var patch struct {
			Content        string `json:"content"`
			HighlightColor string `json:"highlight_color"`
			Status         string `json:"status"`
		}
		if err := json.NewDecoder(e.Request.Body).Decode(&patch); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		if patch.Content != "" {
			record.Set("content", patch.Content)
		}
		if patch.HighlightColor != "" {
			record.Set("highlight_color", patch.HighlightColor)
		}
		if patch.Status != "" {
			record.Set("status", patch.Status)
		}

		if err := app.Save(record); err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to update note: " + err.Error()})
		}

		go exportNotesToGit(app)
		return e.JSON(http.StatusOK, noteRecordToMap(record))
	})

	// DELETE /notes/{noteId} — delete a note
	se.Router.DELETE("/notes/{noteId}", func(e *core.RequestEvent) error {
		noteID := e.Request.PathValue("noteId")
		record, err := app.FindFirstRecordByFilter("notes", "note_id = {:nid}", map[string]any{
			"nid": noteID,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		if err := app.Delete(record); err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "failed to delete note: " + err.Error()})
		}

		go exportNotesToGit(app)
		return e.NoContent(http.StatusNoContent)
	})

	// ── Series routes ──

	// GET /series — list series
	se.Router.GET("/series", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("series")
		if err != nil {
			return e.JSON(http.StatusOK, []any{})
		}

		type seriesEntry struct {
			SeriesID       string   `json:"series_id"`
			Title          string   `json:"title"`
			AuthorUsername string   `json:"author_username"`
			Difficulty     string   `json:"difficulty"`
			Description    string   `json:"description"`
			LessonIDs      []string `json:"lesson_ids"`
			Published      bool     `json:"published"`
		}

		entries := make([]seriesEntry, 0, len(records))
		for _, r := range records {
			entries = append(entries, seriesEntry{
				SeriesID:       r.GetString("series_id"),
				Title:          r.GetString("title"),
				AuthorUsername: r.GetString("author_username"),
				Difficulty:     r.GetString("difficulty"),
				Description:    r.GetString("description"),
				LessonIDs:      getStringSlice(r, "lesson_ids"),
				Published:      r.GetBool("published"),
			})
		}
		return e.JSON(http.StatusOK, entries)
	})

	// GET /series/{id} — get specific series
	se.Router.GET("/series/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		record, err := app.FindFirstRecordByFilter("series", "series_id = {:sid}", map[string]any{
			"sid": id,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		result := map[string]any{
			"series_id":       record.GetString("series_id"),
			"title":           record.GetString("title"),
			"author_username": record.GetString("author_username"),
			"difficulty":      record.GetString("difficulty"),
			"description":     record.GetString("description"),
			"lesson_ids":      getStringSlice(record, "lesson_ids"),
			"published":       record.GetBool("published"),
			"content":         record.GetString("content"),
		}
		return e.JSON(http.StatusOK, result)
	})

	// POST /series — create series via GitStore
	se.Router.POST("/series", func(e *core.RequestEvent) error {
		var s data.Series
		if err := json.NewDecoder(e.Request.Body).Decode(&s); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON: " + err.Error()})
		}
		if s.SeriesID == "" {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "series_id is required"})
		}

		sha, err := gs.AddSeries(s)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusOK, map[string]string{
			"status":     "created",
			"commit_sha": sha,
		})
	})

	// PATCH /series/{id} — update series via GitStore
	se.Router.PATCH("/series/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		var s data.Series
		if err := json.NewDecoder(e.Request.Body).Decode(&s); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON: " + err.Error()})
		}
		s.SeriesID = id

		sha, err := gs.UpdateSeries(id, s)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusOK, map[string]string{
			"status":     "updated",
			"commit_sha": sha,
		})
	})

	// ── Strategy write routes ──

	// POST /strategies — write strategy/memory to git
	se.Router.POST("/strategies", func(e *core.RequestEvent) error {
		var req struct {
			Name    string `json:"name"`
			Content string `json:"content"`
		}
		if err := json.NewDecoder(e.Request.Body).Decode(&req); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON: " + err.Error()})
		}
		if req.Name == "" || req.Content == "" {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "name and content are required"})
		}

		sha, err := gs.AddStrategy(req.Name, []byte(req.Content))
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusOK, map[string]string{
			"status":     "created",
			"commit_sha": sha,
		})
	})

	// POST /strategies/{name}/seal — seal strategy with NFT metadata
	se.Router.POST("/strategies/{name}/seal", func(e *core.RequestEvent) error {
		name := e.Request.PathValue("name")
		if name == "" {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "name is required"})
		}

		var nftMetadata any
		if err := json.NewDecoder(e.Request.Body).Decode(&nftMetadata); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON body"})
		}

		prURL, err := gs.SealStrategy(name, nftMetadata)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusOK, map[string]string{
			"status": "sealed",
			"pr_url": prURL,
		})
	})

	// POST /conjectures — submit conjecture package (tar.gz or git URL)
	se.Router.POST("/conjectures", func(e *core.RequestEvent) error {
		ct := e.Request.Header.Get("Content-Type")

		type conjectureCreateResponse struct {
			Status             string   `json:"status"`
			AddedConjectureIDs []string `json:"added_conjecture_ids"`
			Count              int      `json:"count"`
			BatchID            string   `json:"batch_id"`
			CommitSHA          string   `json:"commit_sha"`
			PRUrl              string   `json:"pr_url"`
			Difficulties       []string `json:"difficulties"`
			ProofAssistants    []string `json:"proof_assistants"`
		}

		var conjectures []data.Conjecture
		var batchID string

		switch {
		case strings.HasPrefix(ct, "application/gzip"):
			tmpDir, err := os.MkdirTemp("", "pkg-tar-*")
			if err != nil {
				return e.JSON(http.StatusInternalServerError, map[string]string{"error": "creating temp dir: " + err.Error()})
			}
			defer os.RemoveAll(tmpDir)

			if err := extractTarGz(e.Request.Body, tmpDir); err != nil {
				return e.JSON(http.StatusBadRequest, map[string]string{"error": "extracting tar.gz: " + err.Error()})
			}

			var loadErr error
			conjectures, loadErr = loadConjecturesFromDir(tmpDir)
			if loadErr != nil {
				return e.JSON(http.StatusBadRequest, map[string]string{"error": loadErr.Error()})
			}
			batchID = uuid.New().String()

		case strings.HasPrefix(ct, "application/json"):
			var body struct {
				GitURL string `json:"git_url"`
			}
			if err := json.NewDecoder(e.Request.Body).Decode(&body); err != nil {
				return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON body: " + err.Error()})
			}
			if body.GitURL == "" {
				return e.JSON(http.StatusBadRequest, map[string]string{"error": "git_url is required"})
			}

			tmpDir, err := os.MkdirTemp("", "pkg-git-*")
			if err != nil {
				return e.JSON(http.StatusInternalServerError, map[string]string{"error": "creating temp dir: " + err.Error()})
			}
			defer os.RemoveAll(tmpDir)

			cmd := exec.Command("git", "clone", "--depth", "1", body.GitURL, tmpDir)
			if out, err := cmd.CombinedOutput(); err != nil {
				return e.JSON(http.StatusBadRequest, map[string]string{"error": fmt.Sprintf("git clone failed: %s: %v", string(out), err)})
			}

			var loadErr error
			conjectures, loadErr = loadConjecturesFromDir(tmpDir)
			if loadErr != nil {
				return e.JSON(http.StatusBadRequest, map[string]string{"error": loadErr.Error()})
			}
			batchID = uuid.New().String()

		default:
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "unsupported content type"})
		}

		submitResult, err := gs.AddConjectures(conjectures, batchID)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "adding conjectures via git: " + err.Error()})
		}

		// Collect metadata
		ids := make([]string, len(conjectures))
		diffSet := map[string]bool{}
		proverSet := map[string]bool{}
		for i, c := range conjectures {
			ids[i] = c.ID
			if c.Difficulty != "" {
				diffSet[c.Difficulty] = true
			}
			if c.Prover != "" {
				proverSet[c.Prover] = true
			}
		}
		var diffs, provers []string
		for d := range diffSet {
			diffs = append(diffs, d)
		}
		for p := range proverSet {
			provers = append(provers, p)
		}
		if diffs == nil {
			diffs = []string{}
		}
		if provers == nil {
			provers = []string{}
		}

		return e.JSON(http.StatusOK, conjectureCreateResponse{
			Status:             "accepted",
			AddedConjectureIDs: ids,
			Count:              len(ids),
			BatchID:            batchID,
			CommitSHA:          submitResult.CommitSHA,
			PRUrl:              submitResult.PRUrl,
			Difficulties:       diffs,
			ProofAssistants:    provers,
		})
	})

	// POST /conjectures/batches/{batchId}/seal — seal conjecture package
	se.Router.POST("/conjectures/batches/{batchId}/seal", func(e *core.RequestEvent) error {
		batchID := e.Request.PathValue("batchId")
		if batchID == "" {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "batchId is required"})
		}

		var nftMetadata any
		if err := json.NewDecoder(e.Request.Body).Decode(&nftMetadata); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON body: " + err.Error()})
		}

		prURL, err := gs.SealConjecturePackage(batchID, nftMetadata)
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusOK, map[string]string{
			"status": "sealed",
			"pr_url": prURL,
		})
	})

	// POST /webhooks/git — webhook handler
	se.Router.POST("/webhooks/git", func(e *core.RequestEvent) error {
		body, err := io.ReadAll(e.Request.Body)
		if err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "failed to read body"})
		}

		// Verify signature
		signature := e.Request.Header.Get("X-Hub-Signature-256")
		if signature == "" {
			signature = e.Request.Header.Get("X-Gitlab-Token")
		}

		if !gs.Forge().VerifyWebhookSignature(body, signature) {
			slog.Warn("Webhook signature verification failed")
			return e.JSON(http.StatusUnauthorized, map[string]string{"error": "invalid signature"})
		}

		// Parse ref
		var payload struct {
			Ref string `json:"ref"`
		}
		if err := json.Unmarshal(body, &payload); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		if payload.Ref != "refs/heads/main" {
			return e.JSON(http.StatusOK, map[string]string{"status": "ignored", "reason": "not main branch"})
		}

		slog.Info("Webhook: push to main detected, rebuilding PocketBase")

		if err := gs.PullAndRebuild(func(repoPath string) error {
			return rebuildFromGit(app)
		}); err != nil {
			slog.Error("Webhook rebuild failed", "error", err)
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "rebuild failed"})
		}

		slog.Info("Webhook: PocketBase rebuild complete")
		return e.JSON(http.StatusOK, map[string]string{"status": "rebuilt"})
	})

	// POST /ai/chat — AI tutor proxy (BYOK)
	se.Router.POST("/ai/chat", func(e *core.RequestEvent) error {
		var req struct {
			Messages []struct {
				Role    string `json:"role"`
				Content string `json:"content"`
			} `json:"messages"`
			ZoneContext  string `json:"zone_context"`
			LessonTitle string `json:"lesson_title"`
			APIKey      string `json:"api_key"`
			Provider    string `json:"provider"`
			Model       string `json:"model"`
			ContextType string `json:"context_type"`
		}
		if err := json.NewDecoder(e.Request.Body).Decode(&req); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid request body"})
		}

		apiKey := req.APIKey
		if apiKey == "" {
			apiKey = cfg.AIAPIKey
		}
		if apiKey == "" {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "API key required"})
		}
		if len(req.Messages) == 0 {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "messages required"})
		}
		if len(req.Messages) > 20 {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "too many messages (max 20)"})
		}

		var systemPrompt string
		if req.ContextType == "selection" {
			systemPrompt = fmt.Sprintf(
				"You are a math tutor helping a student with the lesson '%s'. The student selected the following text and has a question about it:\n\n%s\n\nUse $...$ for inline and $$...$$ for display math. Be concise.",
				req.LessonTitle, req.ZoneContext,
			)
		} else {
			systemPrompt = fmt.Sprintf(
				"You are a math tutor helping a student with %s in '%s'. Use $...$ for inline and $$...$$ for display math. Be concise.",
				req.ZoneContext, req.LessonTitle,
			)
		}

		// Build messages for provider
		type aiMsg struct {
			Role    string `json:"role"`
			Content string `json:"content"`
		}
		messages := make([]aiMsg, len(req.Messages))
		for i, m := range req.Messages {
			messages[i] = aiMsg{Role: m.Role, Content: m.Content}
		}

		var (
			providerURL string
			payload     []byte
			authHeader  string
			authValue   string
		)

		provider := req.Provider
		if provider == "" {
			provider = cfg.AIProvider
		}
		model := req.Model
		if model == "" {
			model = cfg.AIModel
		}
		if model == "" || provider != cfg.AIProvider {
			if provider == "openai" {
				model = "gpt-4o"
			} else {
				model = "claude-sonnet-4-20250514"
			}
		}

		if provider == "openai" {
			allMessages := make([]aiMsg, 0, len(messages)+1)
			allMessages = append(allMessages, aiMsg{Role: "system", Content: systemPrompt})
			allMessages = append(allMessages, messages...)
			payload, _ = json.Marshal(map[string]any{
				"model": model, "max_tokens": 2048, "messages": allMessages,
			})
			providerURL = "https://api.openai.com/v1/chat/completions"
			authHeader = "Authorization"
			authValue = "Bearer " + apiKey
		} else {
			payload, _ = json.Marshal(map[string]any{
				"model": model, "max_tokens": 2048, "system": systemPrompt, "messages": messages,
			})
			providerURL = "https://api.anthropic.com/v1/messages"
			authHeader = "x-api-key"
			authValue = apiKey
		}

		providerReq, err := http.NewRequest("POST", providerURL, bytes.NewReader(payload))
		if err != nil {
			return e.JSON(http.StatusBadGateway, map[string]string{"error": "AI provider error. Try again later."})
		}
		providerReq.Header.Set("Content-Type", "application/json")
		providerReq.Header.Set(authHeader, authValue)
		if provider != "openai" {
			providerReq.Header.Set("anthropic-version", "2023-06-01")
		}

		resp, err := http.DefaultClient.Do(providerReq)
		if err != nil {
			return e.JSON(http.StatusBadGateway, map[string]string{"error": "AI provider error. Try again later."})
		}
		defer resp.Body.Close()

		respBody, _ := io.ReadAll(resp.Body)
		if resp.StatusCode != http.StatusOK {
			var errMsg string
			switch resp.StatusCode {
			case 401:
				errMsg = "API key rejected by provider. Check your key."
			case 429:
				errMsg = "Rate limited by provider. Wait and retry."
			case 402:
				errMsg = "Insufficient credits. Check your provider billing."
			default:
				errMsg = "AI provider error. Try again later."
			}
			return e.JSON(http.StatusBadGateway, map[string]string{"error": errMsg})
		}

		// Parse provider response
		var content string
		if provider == "openai" {
			var result struct {
				Choices []struct {
					Message struct {
						Content string `json:"content"`
					} `json:"message"`
				} `json:"choices"`
			}
			if err := json.Unmarshal(respBody, &result); err != nil || len(result.Choices) == 0 {
				return e.JSON(http.StatusBadGateway, map[string]string{"error": "AI provider error. Try again later."})
			}
			content = result.Choices[0].Message.Content
		} else {
			var result struct {
				Content []struct {
					Text string `json:"text"`
				} `json:"content"`
			}
			if err := json.Unmarshal(respBody, &result); err != nil || len(result.Content) == 0 {
				return e.JSON(http.StatusBadGateway, map[string]string{"error": "AI provider error. Try again later."})
			}
			content = result.Content[0].Text
		}

		return e.JSON(http.StatusOK, map[string]string{"content": content})
	})

	// POST /ai/models — discover models from a provider (BYOK)
	se.Router.POST("/ai/models", func(e *core.RequestEvent) error {
		var req struct {
			Provider string `json:"provider"`
			APIKey   string `json:"api_key"`
		}
		if err := json.NewDecoder(e.Request.Body).Decode(&req); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid request body"})
		}
		if req.APIKey == "" {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "API key required"})
		}
		if req.Provider == "" {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "provider required"})
		}

		var (
			listURL    string
			authHeader string
			authValue  string
		)
		if req.Provider == "openai" {
			listURL = "https://api.openai.com/v1/models"
			authHeader = "Authorization"
			authValue = "Bearer " + req.APIKey
		} else {
			listURL = "https://api.anthropic.com/v1/models?limit=100"
			authHeader = "x-api-key"
			authValue = req.APIKey
		}

		modelsReq, err := http.NewRequest("GET", listURL, nil)
		if err != nil {
			return e.JSON(http.StatusBadGateway, map[string]string{"error": "AI provider error. Try again later."})
		}
		modelsReq.Header.Set(authHeader, authValue)
		if req.Provider != "openai" {
			modelsReq.Header.Set("anthropic-version", "2023-06-01")
		}

		resp, err := http.DefaultClient.Do(modelsReq)
		if err != nil {
			return e.JSON(http.StatusBadGateway, map[string]string{"error": "AI provider error. Try again later."})
		}
		defer resp.Body.Close()

		if resp.StatusCode != http.StatusOK {
			var errMsg string
			switch resp.StatusCode {
			case 401:
				errMsg = "API key rejected by provider. Check your key."
			case 429:
				errMsg = "Rate limited by provider. Wait and retry."
			default:
				errMsg = "AI provider error. Try again later."
			}
			return e.JSON(http.StatusBadGateway, map[string]string{"error": errMsg})
		}

		respBody, _ := io.ReadAll(resp.Body)
		var listResult struct {
			Data []struct {
				ID string `json:"id"`
			} `json:"data"`
		}
		if err := json.Unmarshal(respBody, &listResult); err != nil {
			return e.JSON(http.StatusBadGateway, map[string]string{"error": "AI provider error. Try again later."})
		}

		models := make([]string, 0, len(listResult.Data))
		if req.Provider == "openai" {
			chatPrefixes := []string{"gpt-", "o1-", "o3-", "o4-", "chatgpt-"}
			for _, m := range listResult.Data {
				for _, p := range chatPrefixes {
					if strings.HasPrefix(m.ID, p) {
						models = append(models, m.ID)
						break
					}
				}
			}
		} else {
			for _, m := range listResult.Data {
				models = append(models, m.ID)
			}
		}
		sort.Strings(models)

		return e.JSON(http.StatusOK, map[string]any{"models": models})
	})

	// Serve lesson.html for series-scoped lesson URLs
	se.Router.GET("/series/{seriesId}/lessons/{lessonId}", func(e *core.RequestEvent) error {
		f, err := static.Files.ReadFile("lesson.html")
		if err != nil {
			return e.NotFoundError("", nil)
		}
		e.Response.Header().Set("Content-Type", "text/html; charset=utf-8")
		e.Response.Write(f)
		return nil
	})

	// Serve embedded static files (web UI)
	fileServer := http.FileServer(http.FS(static.Files))
	se.Router.GET("/{path...}", func(e *core.RequestEvent) error {
		fileServer.ServeHTTP(e.Response, e.Request)
		return nil
	})
}

// rebuildFromGit walks the git data repo and upserts all data into PocketBase collections.
// Ported from src/server/store/sqlite/sqlite.go RebuildFromDir().
func rebuildFromGit(app core.App) error {
	hooks.IsRebuilding.Store(true)
	defer hooks.IsRebuilding.Store(false)

	repoPath := gs.RepoPath()

	// Clear existing records
	for _, collName := range []string{"proofs", "certificates", "contributions", "conjectures", "strategies", "expositions", "lessons", "series"} {
		records, err := app.FindAllRecords(collName)
		if err != nil {
			continue
		}
		for _, r := range records {
			app.Delete(r)
		}
	}

	// Walk conjectures/
	conjecturesDir := filepath.Join(repoPath, "conjectures")
	if entries, err := os.ReadDir(conjecturesDir); err == nil {
		collection, colErr := app.FindCollectionByNameOrId("conjectures")
		if colErr == nil {
			for _, entry := range entries {
				ext := filepath.Ext(entry.Name())
				if entry.IsDir() || !data.IsConjectureExt(ext) {
					continue
				}
				// Skip nft_metadata files
				if strings.HasPrefix(entry.Name(), "nft_metadata") {
					continue
				}
				raw, err := os.ReadFile(filepath.Join(conjecturesDir, entry.Name()))
				if err != nil {
					slog.Error("Rebuild: failed to read conjecture", "file", entry.Name(), "error", err)
					continue
				}
				c, err := data.UnmarshalConjecture(raw, ext)
				if err != nil {
					slog.Error("Rebuild: failed to parse conjecture", "file", entry.Name(), "error", err)
					continue
				}
				if c.ID == "" {
					continue
				}
				if c.Status == "" {
					c.Status = "open"
				}

				record := core.NewRecord(collection)
				record.Set("conjecture_id", c.ID)
				record.Set("title", c.Title)
				record.Set("difficulty", c.Difficulty)
				record.Set("prover", c.Prover)
				record.Set("status", c.Status)
				record.Set("preamble", c.Preamble)
				record.Set("lemma_statement", c.LemmaStatement)
				record.Set("hints", c.Hints)
				record.Set("skeleton", c.Skeleton)
				record.Set("dependencies", c.Dependencies)
				if err := app.Save(record); err != nil {
					slog.Error("Rebuild: failed to save conjecture", "id", c.ID, "error", err)
				}
			}
		}
	}

	// Walk contributions/*/summary.json + proofs/*.json
	contributionsDir := filepath.Join(repoPath, "contributions")
	if entries, err := os.ReadDir(contributionsDir); err == nil {
		contribCollection, _ := app.FindCollectionByNameOrId("contributions")
		resultCollection, _ := app.FindCollectionByNameOrId("proofs")

		for _, entry := range entries {
			if !entry.IsDir() {
				continue
			}
			contribID := entry.Name()
			contribDir := filepath.Join(contributionsDir, contribID)

			// Read summary.json
			summaryPath := filepath.Join(contribDir, "summary.json")
			if raw, err := os.ReadFile(summaryPath); err == nil && contribCollection != nil {
				var cs data.Contribution
				if err := json.Unmarshal(raw, &cs); err == nil {
					record := core.NewRecord(contribCollection)
					record.Set("contribution_id", cs.ContributionID)
					record.Set("username", cs.Username)
					record.Set("conjectures_attempted", cs.ConjecturesAttempted)
					record.Set("conjectures_proved", cs.ConjecturesProved)
					record.Set("cost_usd", cs.TotalCostUSD)
					record.Set("archive_sha256", cs.ArchiveSHA256)
					record.Set("nft_metadata", cs.NFTMetadata)
					record.Set("prover", cs.Prover)
					record.Set("conjecture_ids", cs.ConjectureIDs)
					record.Set("proof_status", cs.ProofStatus)
					record.Set("certified_by", cs.CertifiedBy)
					if err := app.Save(record); err != nil {
						slog.Error("Rebuild: failed to save contribution", "id", contribID, "error", err)
					}
				}
			}

			// Read proofs/*.json
			resultsDir := filepath.Join(contribDir, "proofs")
			if resultEntries, err := os.ReadDir(resultsDir); err == nil && resultCollection != nil {
				for _, re := range resultEntries {
					if re.IsDir() || filepath.Ext(re.Name()) != ".json" {
						continue
					}
					raw, err := os.ReadFile(filepath.Join(resultsDir, re.Name()))
					if err != nil {
						continue
					}
					var r data.Proof
					if err := json.Unmarshal(raw, &r); err != nil {
						continue
					}
					if r.ContributionID == "" {
						r.ContributionID = contribID
					}

					record := core.NewRecord(resultCollection)
					record.Set("contribution_id", r.ContributionID)
					record.Set("conjecture_id", r.ConjectureID)
					record.Set("username", r.Username)
					record.Set("success", r.Success)
					record.Set("proof_script", r.ProofScript)
					record.Set("cost_usd", r.CostUSD)
					record.Set("attempts", r.Attempts)
					record.Set("error_output", r.ErrorOutput)
					if err := app.Save(record); err != nil {
						slog.Error("Rebuild: failed to save proof", "error", err)
					}

					// Update conjecture status if proved
					if r.Success && r.ConjectureID != "" {
						conjecture, findErr := app.FindFirstRecordByFilter("conjectures", "conjecture_id = {:pid}", map[string]any{
							"pid": r.ConjectureID,
						})
						if findErr == nil {
							conjecture.Set("status", "proved")
							app.Save(conjecture)
						}
					}
				}
			}
		}
	}

	// Walk certificates/*/summary.json
	certificatesDir := filepath.Join(repoPath, "certificates")
	if entries, err := os.ReadDir(certificatesDir); err == nil {
		certCollection, _ := app.FindCollectionByNameOrId("certificates")
		if certCollection != nil {
			for _, entry := range entries {
				if !entry.IsDir() {
					continue
				}
				summaryPath := filepath.Join(certificatesDir, entry.Name(), "summary.json")
				raw, err := os.ReadFile(summaryPath)
				if err != nil {
					continue
				}
				var cs data.Certificate
				if err := json.Unmarshal(raw, &cs); err != nil {
					continue
				}

				record := core.NewRecord(certCollection)
				record.Set("certificate_id", cs.CertificateID)
				record.Set("certifier_username", cs.CertifierUsername)
				record.Set("packages_certified", cs.PackagesCertified)
				record.Set("conjectures_compared", cs.ConjecturesCompared)
				record.Set("package_rankings", cs.PackageRankings)
				record.Set("recommendation", cs.Recommendation)
				record.Set("archive_sha256", cs.ArchiveSHA256)
				record.Set("nft_metadata", cs.NFTMetadata)
				if err := app.Save(record); err != nil {
					slog.Error("Rebuild: failed to save certificate", "id", cs.CertificateID, "error", err)
				}

				// Update certified_by for contributions referenced in rankings
				for _, pr := range cs.PackageRankings {
					contribution, findErr := app.FindFirstRecordByFilter("contributions", "contribution_id = {:cid}", map[string]any{
						"cid": pr.ContributorContributionID,
					})
					if findErr != nil {
						continue
					}

					certifiers := getStringSlice(contribution, "certified_by")
					found := false
					for _, c := range certifiers {
						if c == cs.CertifierUsername {
							found = true
							break
						}
					}
					if !found {
						certifiers = append(certifiers, cs.CertifierUsername)
						contribution.Set("certified_by", certifiers)
						app.Save(contribution)
					}
				}
			}
		}
	}

	// Walk expositions/*/summary.json
	expositionsDir := filepath.Join(repoPath, "expositions")
	if entries, err := os.ReadDir(expositionsDir); err == nil {
		expoCollection, _ := app.FindCollectionByNameOrId("expositions")
		if expoCollection != nil {
			for _, entry := range entries {
				if !entry.IsDir() {
					continue
				}
				summaryPath := filepath.Join(expositionsDir, entry.Name(), "summary.json")
				raw, err := os.ReadFile(summaryPath)
				if err != nil {
					continue
				}
				var ex data.Exposition
				if err := json.Unmarshal(raw, &ex); err != nil {
					continue
				}

				record := core.NewRecord(expoCollection)
				record.Set("exposition_id", ex.ExpositionID)
				record.Set("author_username", ex.AuthorUsername)
				record.Set("contribution_id", ex.ContributionID)
				record.Set("conjecture_id", ex.ConjectureID)
				record.Set("prover", ex.Prover)
				record.Set("proof_script", ex.ProofScript)
				record.Set("exposition_text", ex.ExpositionText)
				record.Set("cost_usd", ex.CostUSD)
				record.Set("strategy_used", ex.StrategyUsed)
				record.Set("nft_metadata", ex.NFTMetadata)
				record.Set("domain", ex.Domain)
				record.Set("title", ex.Title)
				record.Set("summary", ex.Summary)
				if err := app.Save(record); err != nil {
					slog.Error("Rebuild: failed to save exposition", "id", ex.ExpositionID, "error", err)
				}
			}
		}
	}

	// Walk visualizations/*/summary.json — migrate into expositions
	visualizationsDir := filepath.Join(repoPath, "visualizations")
	if entries, err := os.ReadDir(visualizationsDir); err == nil {
		vizExpoCollection, _ := app.FindCollectionByNameOrId("expositions")
		if vizExpoCollection != nil {
			for _, entry := range entries {
				if !entry.IsDir() {
					continue
				}
				summaryPath := filepath.Join(visualizationsDir, entry.Name(), "summary.json")
				raw, err := os.ReadFile(summaryPath)
				if err != nil {
					continue
				}
				var parsed map[string]any
				if err := json.Unmarshal(raw, &parsed); err != nil {
					continue
				}

				record := core.NewRecord(vizExpoCollection)
				record.Set("exposition_id", parsed["visualization_id"])
				record.Set("author_username", parsed["author_username"])
				record.Set("conjecture_id", parsed["conjecture_id"])
				record.Set("domain", parsed["domain"])
				record.Set("title", parsed["title"])
				record.Set("summary", parsed["summary"])
				record.Set("exposition_text", parsed["viz_json"])
				record.Set("cost_usd", parsed["cost_usd"])
				record.Set("strategy_used", parsed["strategy_used"])
				record.Set("nft_metadata", parsed["nft_metadata"])
				if err := app.Save(record); err != nil {
					vizID, _ := parsed["visualization_id"].(string)
					slog.Error("Rebuild: failed to save migrated visualization", "id", vizID, "error", err)
				}
			}
		}
	}

	// Walk strategies/*.md
	strategiesDir := filepath.Join(repoPath, "strategies")
	if entries, err := os.ReadDir(strategiesDir); err == nil {
		strategyCollection, _ := app.FindCollectionByNameOrId("strategies")
		if strategyCollection != nil {
			for _, entry := range entries {
				if entry.IsDir() || filepath.Ext(entry.Name()) != ".md" {
					continue
				}
				raw, err := os.ReadFile(filepath.Join(strategiesDir, entry.Name()))
				if err != nil {
					slog.Error("Rebuild: failed to read strategy", "file", entry.Name(), "error", err)
					continue
				}
				strat, err := parseStrategyMD(raw, entry.Name())
				if err != nil {
					slog.Error("Rebuild: failed to parse strategy", "file", entry.Name(), "error", err)
					continue
				}

				record := core.NewRecord(strategyCollection)
				record.Set("name", strat.Name)
				record.Set("kind", strat.Kind)
				record.Set("prover", strat.Prover)
				record.Set("description", strat.Description)
				record.Set("priority", strat.Priority)
				record.Set("body", strat.Body)
				if err := app.Save(record); err != nil {
					slog.Error("Rebuild: failed to save strategy", "name", strat.Name, "error", err)
				}
			}
		}
	}

	// Walk lessons/*/lesson.md
	lessonsDir := filepath.Join(repoPath, "lessons")
	if entries, err := os.ReadDir(lessonsDir); err == nil {
		lessonCollection, _ := app.FindCollectionByNameOrId("lessons")
		if lessonCollection != nil {
			for _, entry := range entries {
				if !entry.IsDir() {
					continue
				}
				lessonPath := filepath.Join(lessonsDir, entry.Name(), "lesson.md")
				raw, err := os.ReadFile(lessonPath)
				if err != nil {
					continue
				}
				lesson, err := data.ParseLessonFile(raw)
				if err != nil {
					slog.Error("Rebuild: failed to parse lesson", "dir", entry.Name(), "error", err)
					continue
				}
				if lesson.LessonID == "" {
					lesson.LessonID = entry.Name()
				}

				record := core.NewRecord(lessonCollection)
				record.Set("lesson_id", lesson.LessonID)
				record.Set("author_username", lesson.AuthorUsername)
				record.Set("title", lesson.Title)
				record.Set("topic", lesson.Topic)
				record.Set("difficulty", lesson.Difficulty)
				record.Set("description", lesson.Description)
				record.Set("prerequisites", lesson.Prerequisites)
				record.Set("conjecture_ids", lesson.ConjectureIDs)
				record.Set("published", lesson.Published)
				record.Set("content", lesson.Content)
				record.Set("ai_annotations", lesson.AIAnnotations)
				if err := app.Save(record); err != nil {
					slog.Error("Rebuild: failed to save lesson", "id", lesson.LessonID, "error", err)
				}
			}
		}
	}

	// Walk series/*/series.md
	seriesDir := filepath.Join(repoPath, "series")
	if entries, err := os.ReadDir(seriesDir); err == nil {
		seriesCollection, _ := app.FindCollectionByNameOrId("series")
		if seriesCollection != nil {
			for _, entry := range entries {
				if !entry.IsDir() {
					continue
				}
				seriesPath := filepath.Join(seriesDir, entry.Name(), "series.md")
				raw, err := os.ReadFile(seriesPath)
				if err != nil {
					continue
				}
				s, err := data.ParseSeriesFile(raw)
				if err != nil {
					slog.Error("Rebuild: failed to parse series", "dir", entry.Name(), "error", err)
					continue
				}
				if s.SeriesID == "" {
					s.SeriesID = entry.Name()
				}

				record := core.NewRecord(seriesCollection)
				record.Set("series_id", s.SeriesID)
				record.Set("title", s.Title)
				record.Set("author_username", s.AuthorUsername)
				record.Set("difficulty", s.Difficulty)
				record.Set("description", s.Description)
				record.Set("lesson_ids", s.LessonIDs)
				record.Set("published", s.Published)
				record.Set("content", s.Content)
				if err := app.Save(record); err != nil {
					slog.Error("Rebuild: failed to save series", "id", s.SeriesID, "error", err)
				}
			}
		}
	}

	// Also seed conjectures from CONJECTURES_DIR if not already loaded from git
	seedConjectures(app)

	// Seed demo expositions from EXPOSITIONS_DIR if not already loaded from git
	seedExpositions(app)

	// Seed lessons from LESSONS_DIR if not already loaded from git
	seedLessons(app)

	// Seed series from SERIES_DIR if not already loaded from git
	seedSeries(app)

	slog.Info("PocketBase rebuild from git complete", "path", repoPath)
	return nil
}

// seedConjectures loads conjecture JSON files from the CONJECTURES_DIR directory.
func seedConjectures(app core.App) {
	dir := os.Getenv("CONJECTURES_DIR")
	if dir == "" {
		dir = "conjectures"
	}

	entries, err := os.ReadDir(dir)
	if err != nil {
		return
	}

	collection, err := app.FindCollectionByNameOrId("conjectures")
	if err != nil {
		return
	}

	for _, entry := range entries {
		ext := filepath.Ext(entry.Name())
		if entry.IsDir() || !data.IsConjectureExt(ext) {
			continue
		}
		if strings.HasPrefix(entry.Name(), "nft_metadata") {
			continue
		}

		raw, err := os.ReadFile(filepath.Join(dir, entry.Name()))
		if err != nil {
			continue
		}

		c, err := data.UnmarshalConjecture(raw, ext)
		if err != nil || c.ID == "" {
			continue
		}

		// Skip if already exists
		existing, _ := app.FindFirstRecordByFilter("conjectures", "conjecture_id = {:pid}", map[string]any{
			"pid": c.ID,
		})
		if existing != nil {
			continue
		}

		status := c.Status
		if status == "" {
			status = "open"
		}

		record := core.NewRecord(collection)
		record.Set("conjecture_id", c.ID)
		record.Set("title", c.Title)
		record.Set("difficulty", c.Difficulty)
		record.Set("prover", c.Prover)
		record.Set("status", status)
		record.Set("preamble", c.Preamble)
		record.Set("lemma_statement", c.LemmaStatement)
		record.Set("hints", c.Hints)
		record.Set("skeleton", c.Skeleton)
		record.Set("dependencies", c.Dependencies)

		app.Save(record)
	}
}

// seedExpositions loads exposition JSON files from the EXPOSITIONS_DIR directory.
func seedExpositions(app core.App) {
	dir := os.Getenv("EXPOSITIONS_DIR")
	if dir == "" {
		dir = "expositions"
	}

	entries, err := os.ReadDir(dir)
	if err != nil {
		return
	}

	collection, err := app.FindCollectionByNameOrId("expositions")
	if err != nil {
		return
	}

	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		summaryPath := filepath.Join(dir, entry.Name(), "summary.json")
		raw, err := os.ReadFile(summaryPath)
		if err != nil {
			continue
		}

		var ex data.Exposition
		if err := json.Unmarshal(raw, &ex); err != nil || ex.ExpositionID == "" {
			continue
		}

		// Upsert: update if exists, create if not
		existing, _ := app.FindFirstRecordByFilter("expositions", "exposition_id = {:eid}", map[string]any{
			"eid": ex.ExpositionID,
		})

		record := existing
		if record == nil {
			record = core.NewRecord(collection)
			record.Set("exposition_id", ex.ExpositionID)
		}
		record.Set("author_username", ex.AuthorUsername)
		record.Set("contribution_id", ex.ContributionID)
		record.Set("conjecture_id", ex.ConjectureID)
		record.Set("prover", ex.Prover)
		record.Set("proof_script", ex.ProofScript)
		record.Set("exposition_text", ex.ExpositionText)
		record.Set("cost_usd", ex.CostUSD)
		record.Set("strategy_used", ex.StrategyUsed)
		record.Set("nft_metadata", ex.NFTMetadata)
		record.Set("domain", ex.Domain)
		record.Set("title", ex.Title)
		record.Set("summary", ex.Summary)

		app.Save(record)
	}
}

// seedLessons loads lesson markdown files from the LESSONS_DIR directory.
func seedLessons(app core.App) {
	dir := os.Getenv("LESSONS_DIR")
	if dir == "" {
		dir = "lessons"
	}
	slog.Info("seedLessons: starting", "dir", dir, "LESSONS_DIR", os.Getenv("LESSONS_DIR"))

	entries, err := os.ReadDir(dir)
	if err != nil {
		slog.Error("seedLessons: ReadDir failed", "dir", dir, "err", err)
		return
	}
	slog.Info("seedLessons: ReadDir OK", "count", len(entries))

	collection, err := app.FindCollectionByNameOrId("lessons")
	if err != nil {
		slog.Error("seedLessons: collection lookup failed", "err", err)
		return
	}

	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		lessonPath := filepath.Join(dir, entry.Name(), "lesson.md")
		raw, err := os.ReadFile(lessonPath)
		if err != nil {
			slog.Warn("seedLessons: ReadFile failed", "path", lessonPath, "err", err)
			continue
		}
		lesson, err := data.ParseLessonFile(raw)
		if err != nil {
			slog.Error("seedLessons: ParseLessonFile failed", "path", lessonPath, "err", err)
			continue
		}
		if lesson.LessonID == "" {
			lesson.LessonID = entry.Name()
		}

		// Skip if already loaded from git
		existing, _ := app.FindFirstRecordByFilter("lessons", "lesson_id = {:lid}", map[string]any{
			"lid": lesson.LessonID,
		})
		if existing != nil {
			slog.Info("seedLessons: skipping existing", "lesson_id", lesson.LessonID)
			continue
		}

		record := core.NewRecord(collection)
		record.Set("lesson_id", lesson.LessonID)
		record.Set("author_username", lesson.AuthorUsername)
		record.Set("title", lesson.Title)
		record.Set("topic", lesson.Topic)
		record.Set("difficulty", lesson.Difficulty)
		record.Set("description", lesson.Description)
		record.Set("prerequisites", lesson.Prerequisites)
		record.Set("conjecture_ids", lesson.ConjectureIDs)
		record.Set("published", lesson.Published)
		record.Set("content", lesson.Content)
		record.Set("ai_annotations", lesson.AIAnnotations)
		if err := app.Save(record); err != nil {
			slog.Error("seedLessons: Save failed", "lesson_id", lesson.LessonID, "err", err)
			continue
		}
		slog.Info("seedLessons: saved lesson", "lesson_id", lesson.LessonID, "title", lesson.Title)
	}
}

// seedSeries loads series markdown files from the SERIES_DIR directory.
func seedSeries(app core.App) {
	dir := os.Getenv("SERIES_DIR")
	if dir == "" {
		dir = "series"
	}
	slog.Info("seedSeries: starting", "dir", dir)

	entries, err := os.ReadDir(dir)
	if err != nil {
		slog.Error("seedSeries: ReadDir failed", "dir", dir, "err", err)
		return
	}

	collection, err := app.FindCollectionByNameOrId("series")
	if err != nil {
		slog.Error("seedSeries: collection lookup failed", "err", err)
		return
	}

	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		seriesPath := filepath.Join(dir, entry.Name(), "series.md")
		raw, err := os.ReadFile(seriesPath)
		if err != nil {
			continue
		}
		s, err := data.ParseSeriesFile(raw)
		if err != nil {
			slog.Error("seedSeries: ParseSeriesFile failed", "path", seriesPath, "err", err)
			continue
		}
		if s.SeriesID == "" {
			s.SeriesID = entry.Name()
		}

		// Skip if already loaded from git
		existing, _ := app.FindFirstRecordByFilter("series", "series_id = {:sid}", map[string]any{
			"sid": s.SeriesID,
		})
		if existing != nil {
			slog.Info("seedSeries: skipping existing", "series_id", s.SeriesID)
			continue
		}

		record := core.NewRecord(collection)
		record.Set("series_id", s.SeriesID)
		record.Set("title", s.Title)
		record.Set("author_username", s.AuthorUsername)
		record.Set("difficulty", s.Difficulty)
		record.Set("description", s.Description)
		record.Set("lesson_ids", s.LessonIDs)
		record.Set("published", s.Published)
		record.Set("content", s.Content)
		if err := app.Save(record); err != nil {
			slog.Error("seedSeries: Save failed", "series_id", s.SeriesID, "err", err)
			continue
		}
		slog.Info("seedSeries: saved series", "series_id", s.SeriesID, "title", s.Title)
	}
}

// ── Helpers for conjecture package submission ──

func extractTarGz(r io.Reader, destDir string) error {
	gz, err := gzip.NewReader(r)
	if err != nil {
		return err
	}
	defer gz.Close()

	tr := tar.NewReader(gz)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}

		clean := filepath.Clean(hdr.Name)
		if strings.HasPrefix(clean, "..") || strings.Contains(clean, string(filepath.Separator)+"..") {
			continue
		}

		target := filepath.Join(destDir, clean)
		if !strings.HasPrefix(target, destDir) {
			continue
		}

		switch hdr.Typeflag {
		case tar.TypeDir:
			os.MkdirAll(target, 0o755)
		case tar.TypeReg:
			os.MkdirAll(filepath.Dir(target), 0o755)
			f, err := os.Create(target)
			if err != nil {
				return err
			}
			if _, err := io.Copy(f, tr); err != nil {
				f.Close()
				return err
			}
			f.Close()
		}
	}
	return nil
}

func loadConjecturesFromDir(dir string) ([]data.Conjecture, error) {
	var conjectures []data.Conjecture
	err := filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil
		}
		if info.IsDir() || filepath.Ext(path) != ".json" {
			return nil
		}
		raw, err := os.ReadFile(path)
		if err != nil {
			return nil
		}
		var c data.Conjecture
		if err := json.Unmarshal(raw, &c); err != nil {
			return nil
		}
		if c.ID == "" {
			return nil
		}
		conjectures = append(conjectures, c)
		return nil
	})
	if err != nil {
		return nil, fmt.Errorf("walking directory: %w", err)
	}
	return conjectures, nil
}

// parseStrategyMD parses a .md strategy file with TOML frontmatter (between +++ delimiters).
func parseStrategyMD(raw []byte, filename string) (data.Strategy, error) {
	content := string(raw)
	if !strings.HasPrefix(content, "+++\n") {
		return data.Strategy{}, fmt.Errorf("missing +++ frontmatter delimiter")
	}
	rest := content[4:]
	endIdx := strings.Index(rest, "\n+++\n")
	if endIdx < 0 {
		return data.Strategy{}, fmt.Errorf("missing closing +++ frontmatter delimiter")
	}
	frontmatter := rest[:endIdx]
	body := strings.TrimLeft(rest[endIdx+4:], "\n")

	var cmd data.Strategy
	cmd.Body = body

	for _, line := range strings.Split(frontmatter, "\n") {
		line = strings.TrimSpace(line)
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		parts := strings.SplitN(line, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key := strings.TrimSpace(parts[0])
		val := strings.TrimSpace(parts[1])
		val = strings.Trim(val, "\"")

		switch key {
		case "name":
			cmd.Name = val
		case "kind":
			cmd.Kind = val
		case "prover":
			cmd.Prover = val
		case "description":
			cmd.Description = val
		case "priority":
			if n, err := strconv.Atoi(val); err == nil {
				cmd.Priority = n
			}
		}
	}

	if cmd.Name == "" {
		cmd.Name = strings.TrimSuffix(filename, ".md")
	}
	return cmd, nil
}
