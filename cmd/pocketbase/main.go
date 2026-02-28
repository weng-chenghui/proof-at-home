package main

import (
	"archive/tar"
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

var (
	gs    *gitstore.GitStore
	forge gitstore.ForgeClient
)

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

	// Register migration system
	migratecmd.MustRegister(app, app.RootCmd, migratecmd.Config{
		Dir:         "cmd/pocketbase/migrations",
		Automigrate: true,
	})

	// Register business logic hooks
	hooks.Register(app)

	// Register custom API routes
	app.OnServe().BindFunc(func(se *core.ServeEvent) error {
		registerRoutes(se, app)
		return se.Next()
	})

	// Rebuild PocketBase from git on startup
	app.OnServe().BindFunc(func(se *core.ServeEvent) error {
		slog.Info("Rebuilding PocketBase from git data on startup")
		if err := rebuildFromGit(app); err != nil {
			slog.Error("Failed to rebuild from git on startup", "error", err)
		}

		// Wire up LocalForge rebuild callback
		if lf, ok := forge.(*gitstore.LocalForge); ok {
			lf.SetRebuildFn(func(repoPath string) error {
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
// with the existing proof-at-home client.
func registerRoutes(se *core.ServeEvent, app core.App) {
	// ── Read routes (PocketBase as cache) ──

	// GET /health
	se.Router.GET("/health", func(e *core.RequestEvent) error {
		return e.JSON(http.StatusOK, map[string]string{"status": "ok"})
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
			var conjectureIDs []string
			if raw := r.Get("conjecture_ids"); raw != nil {
				if list, ok := raw.([]any); ok {
					for _, v := range list {
						if s, ok := v.(string); ok {
							conjectureIDs = append(conjectureIDs, s)
						}
					}
				}
			}
			var certifiedBy []string
			if raw := r.Get("certified_by"); raw != nil {
				if list, ok := raw.([]any); ok {
					for _, v := range list {
						if s, ok := v.(string); ok {
							certifiedBy = append(certifiedBy, s)
						}
					}
				}
			}
			entries = append(entries, contributionEntry{
				ContributionID:       r.GetString("contribution_id"),
				Username:             r.GetString("username"),
				ConjecturesAttempted: int(r.GetFloat("conjectures_attempted")),
				ConjecturesProved:    int(r.GetFloat("conjectures_proved")),
				TotalCostUSD:         r.GetFloat("cost_usd"),
				ArchiveSHA256:        r.GetString("archive_sha256"),
				Prover:               r.GetString("prover"),
				ConjectureIDs:        conjectureIDs,
				ProofStatus:          r.GetString("proof_status"),
				CertifiedBy:          certifiedBy,
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

		var conjectureIDs []string
		if raw := record.Get("conjecture_ids"); raw != nil {
			if list, ok := raw.([]any); ok {
				for _, v := range list {
					if s, ok := v.(string); ok {
						conjectureIDs = append(conjectureIDs, s)
					}
				}
			}
		}
		var certifiedBy []string
		if raw := record.Get("certified_by"); raw != nil {
			if list, ok := raw.([]any); ok {
				for _, v := range list {
					if s, ok := v.(string); ok {
						certifiedBy = append(certifiedBy, s)
					}
				}
			}
		}

		result := map[string]any{
			"contribution_id":       record.GetString("contribution_id"),
			"username":              record.GetString("username"),
			"conjectures_attempted": int(record.GetFloat("conjectures_attempted")),
			"conjectures_proved":    int(record.GetFloat("conjectures_proved")),
			"total_cost_usd":        record.GetFloat("cost_usd"),
			"archive_sha256":        record.GetString("archive_sha256"),
			"prover":                record.GetString("prover"),
			"conjecture_ids":        conjectureIDs,
			"proof_status":          record.GetString("proof_status"),
			"certified_by":          certifiedBy,
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

			var conjectureIDs []string
			if raw := r.Get("conjecture_ids"); raw != nil {
				if list, ok := raw.([]any); ok {
					for _, v := range list {
						if s, ok := v.(string); ok {
							conjectureIDs = append(conjectureIDs, s)
						}
					}
				}
			}

			var certifiedBy []string
			if raw := r.Get("certified_by"); raw != nil {
				if list, ok := raw.([]any); ok {
					for _, v := range list {
						if s, ok := v.(string); ok {
							certifiedBy = append(certifiedBy, s)
						}
					}
				}
			}

			packages = append(packages, certPkg{
				ContributorContributionID: contributionID,
				ContributorUsername:       r.GetString("username"),
				Prover:                    prover,
				ConjectureIDs:             conjectureIDs,
				ArchiveURL:                "/contributions/" + contributionID + "/archive",
				ArchiveSHA256:             r.GetString("archive_sha256"),
				ProofStatus:               r.GetString("proof_status"),
				CertifiedBy:               certifiedBy,
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
	for _, collName := range []string{"proofs", "certificates", "contributions", "conjectures", "strategies"} {
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
				if entry.IsDir() || filepath.Ext(entry.Name()) != ".json" {
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
				var c data.Conjecture
				if err := json.Unmarshal(raw, &c); err != nil {
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

					certifiedBy := contribution.Get("certified_by")
					certifiers, _ := certifiedBy.([]any)
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

	// Also seed conjectures from CONJECTURES_DIR if not already loaded from git
	seedConjectures(app)

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
		if entry.IsDir() || filepath.Ext(entry.Name()) != ".json" {
			continue
		}
		if strings.HasPrefix(entry.Name(), "nft_metadata") {
			continue
		}

		raw, err := os.ReadFile(filepath.Join(dir, entry.Name()))
		if err != nil {
			continue
		}

		var p struct {
			ID             string          `json:"id"`
			Title          string          `json:"title"`
			Difficulty     string          `json:"difficulty"`
			Prover         string          `json:"prover"`
			Status         string          `json:"status"`
			Preamble       string          `json:"preamble"`
			LemmaStatement string          `json:"lemma_statement"`
			Hints          json.RawMessage `json:"hints"`
			Skeleton       string          `json:"skeleton"`
			Dependencies   json.RawMessage `json:"dependencies"`
		}
		if err := json.Unmarshal(raw, &p); err != nil || p.ID == "" {
			continue
		}

		// Skip if already exists
		existing, _ := app.FindFirstRecordByFilter("conjectures", "conjecture_id = {:pid}", map[string]any{
			"pid": p.ID,
		})
		if existing != nil {
			continue
		}

		status := p.Status
		if status == "" {
			status = "open"
		}

		record := core.NewRecord(collection)
		record.Set("conjecture_id", p.ID)
		record.Set("title", p.Title)
		record.Set("difficulty", p.Difficulty)
		record.Set("prover", p.Prover)
		record.Set("status", status)
		record.Set("preamble", p.Preamble)
		record.Set("lemma_statement", p.LemmaStatement)
		record.Set("hints", p.Hints)
		record.Set("skeleton", p.Skeleton)
		record.Set("dependencies", p.Dependencies)

		app.Save(record)
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
