package main

import (
	"encoding/json"
	"log"
	"net/http"
	"os"
	"path/filepath"

	"github.com/pocketbase/pocketbase"
	"github.com/pocketbase/pocketbase/apis"
	"github.com/pocketbase/pocketbase/core"
	"github.com/pocketbase/pocketbase/plugins/migratecmd"

	"github.com/proof-at-home/server/cmd/pocketbase/hooks"
	_ "github.com/proof-at-home/server/cmd/pocketbase/migrations"
	"github.com/proof-at-home/server/src/server/static"
)

func main() {
	app := pocketbase.New()

	// Register migration system
	migratecmd.MustRegister(app, app.RootCmd, migratecmd.Config{
		Dir:         "cmd/pocketbase/migrations",
		Automigrate: true,
	})

	// Register business logic hooks
	hooks.Register(app)

	// Register custom API routes that match the existing server's endpoints
	app.OnServe().BindFunc(func(se *core.ServeEvent) error {
		registerRoutes(se, app)
		return se.Next()
	})

	if err := app.Start(); err != nil {
		log.Fatal(err)
	}
}

// registerRoutes adds custom routes that preserve backward compatibility
// with the existing proof-at-home client.
//
// PocketBase auto-generates CRUD at /api/collections/{name}/records,
// but clients expect the original REST paths. These routes bridge the gap.
func registerRoutes(se *core.ServeEvent, app core.App) {
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

	// POST /certificates — submit individual proof result
	se.Router.POST("/certificates", func(e *core.RequestEvent) error {
		var body struct {
			ConjectureID string  `json:"conjecture_id"`
			Username     string  `json:"username"`
			Success      bool    `json:"success"`
			ProofScript  string  `json:"proof_script"`
			CostUSD      float64 `json:"cost_usd"`
			Attempts     int     `json:"attempts"`
			ErrorOutput  string  `json:"error_output"`
		}
		if err := e.BindBody(&body); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		collection, err := app.FindCollectionByNameOrId("certificates")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		record := core.NewRecord(collection)
		record.Set("conjecture_id", body.ConjectureID)
		record.Set("username", body.Username)
		record.Set("success", body.Success)
		record.Set("proof_script", body.ProofScript)
		record.Set("cost_usd", body.CostUSD)
		record.Set("attempts", body.Attempts)
		record.Set("error_output", body.ErrorOutput)

		if err := app.Save(record); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{"status": "accepted"})
	})

	// POST /certificates/batch — submit contribution summary
	se.Router.POST("/certificates/batch", func(e *core.RequestEvent) error {
		var body struct {
			Username            string   `json:"username"`
			ContributionID      string   `json:"contribution_id"`
			ConjecturesAttempted int      `json:"conjectures_attempted"`
			ConjecturesProved    int      `json:"conjectures_proved"`
			TotalCostUSD        float64  `json:"total_cost_usd"`
			ArchiveSHA256       string   `json:"archive_sha256"`
			NFTMetadata         any      `json:"nft_metadata"`
			Prover              string   `json:"prover"`
			ConjectureIDs       []string `json:"conjecture_ids"`
			ArchivePath         string   `json:"archive_path"`
			ProofStatus         string   `json:"proof_status"`
			ReviewedBy          []string `json:"reviewed_by"`
		}
		if err := e.BindBody(&body); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		collection, err := app.FindCollectionByNameOrId("contributions")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		record := core.NewRecord(collection)
		record.Set("contribution_id", body.ContributionID)
		record.Set("username", body.Username)
		record.Set("conjectures_attempted", body.ConjecturesAttempted)
		record.Set("conjectures_proved", body.ConjecturesProved)
		record.Set("cost_usd", body.TotalCostUSD)
		record.Set("archive_sha256", body.ArchiveSHA256)
		record.Set("nft_metadata", body.NFTMetadata)
		record.Set("prover", body.Prover)
		record.Set("conjecture_ids", body.ConjectureIDs)
		record.Set("proof_status", body.ProofStatus)
		record.Set("reviewed_by", body.ReviewedBy)

		if err := app.Save(record); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{"status": "accepted"})
	})

	// GET /review-packages — list review packages
	se.Router.GET("/review-packages", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("contributions")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type reviewPkg struct {
			ProverContributionID string   `json:"prover_contribution_id"`
			ProverUsername       string   `json:"prover_username"`
			Prover               string   `json:"prover"`
			ConjectureIDs        []string `json:"conjecture_ids"`
			ArchiveURL           string   `json:"archive_url"`
			ArchiveSHA256        string   `json:"archive_sha256"`
			ProofStatus          string   `json:"proof_status,omitempty"`
			ReviewedBy           []string `json:"reviewed_by,omitempty"`
		}

		packages := make([]reviewPkg, 0, len(records))
		for _, r := range records {
			contributionID := r.GetString("contribution_id")

			prover := r.GetString("prover")
			if prover == "" {
				prover = "rocq"
			}

			// Get conjecture_ids from JSON field
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

			// Get reviewed_by from JSON field
			var reviewedBy []string
			if raw := r.Get("reviewed_by"); raw != nil {
				if list, ok := raw.([]any); ok {
					for _, v := range list {
						if s, ok := v.(string); ok {
							reviewedBy = append(reviewedBy, s)
						}
					}
				}
			}

			packages = append(packages, reviewPkg{
				ProverContributionID: contributionID,
				ProverUsername:       r.GetString("username"),
				Prover:               prover,
				ConjectureIDs:        conjectureIDs,
				ArchiveURL:           "/review-packages/" + contributionID + "/archive",
				ArchiveSHA256:        r.GetString("archive_sha256"),
				ProofStatus:          r.GetString("proof_status"),
				ReviewedBy:           reviewedBy,
			})
		}
		return e.JSON(http.StatusOK, packages)
	})

	// GET /review-packages/{contributionID}/archive — download archive
	se.Router.GET("/review-packages/{contributionID}/archive", func(e *core.RequestEvent) error {
		contributionID := e.Request.PathValue("contributionID")

		record, err := app.FindFirstRecordByFilter("contributions", "contribution_id = {:cid}", map[string]any{
			"cid": contributionID,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "archive not found"})
		}

		archiveFile := record.GetString("archive")
		if archiveFile == "" {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "archive not found"})
		}

		// Serve the file through PocketBase's filesystem
		fsys, err := app.NewFilesystem()
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": "storage error"})
		}
		defer fsys.Close()

		filePath := record.BaseFilesPath() + "/" + archiveFile
		return fsys.Serve(e.Response, e.Request, filePath, "proofs.tar.gz")
	})

	// POST /reviews — submit review
	se.Router.POST("/reviews", func(e *core.RequestEvent) error {
		var body struct {
			ReviewerUsername   string `json:"reviewer_username"`
			ReviewID           string `json:"review_id"`
			PackagesReviewed   int    `json:"packages_reviewed"`
			ConjecturesCompared int    `json:"conjectures_compared"`
			PackageRankings    []any  `json:"package_rankings"`
			Recommendation     string `json:"recommendation"`
			ArchiveSHA256      string `json:"archive_sha256"`
			NFTMetadata        any    `json:"nft_metadata"`
		}
		if err := e.BindBody(&body); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		collection, err := app.FindCollectionByNameOrId("reviews")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		record := core.NewRecord(collection)
		record.Set("review_id", body.ReviewID)
		record.Set("reviewer_username", body.ReviewerUsername)
		record.Set("packages_reviewed", body.PackagesReviewed)
		record.Set("conjectures_compared", body.ConjecturesCompared)
		record.Set("package_rankings", body.PackageRankings)
		record.Set("recommendation", body.Recommendation)
		record.Set("archive_sha256", body.ArchiveSHA256)
		record.Set("nft_metadata", body.NFTMetadata)

		if err := app.Save(record); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{"status": "accepted"})
	})

	// GET /contributions — list contributions with nft_metadata (for NFT gallery)
	se.Router.GET("/contributions", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("contributions")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type contributionEntry struct {
			ContributionID      string `json:"contribution_id"`
			Username            string `json:"username"`
			ConjecturesAttempted int    `json:"conjectures_attempted"`
			ConjecturesProved    int    `json:"conjectures_proved"`
			Prover              string `json:"prover"`
			ProofStatus         string `json:"proof_status"`
			NFTMetadata         any    `json:"nft_metadata"`
		}

		entries := make([]contributionEntry, 0, len(records))
		for _, r := range records {
			entries = append(entries, contributionEntry{
				ContributionID:      r.GetString("contribution_id"),
				Username:            r.GetString("username"),
				ConjecturesAttempted: int(r.GetFloat("conjectures_attempted")),
				ConjecturesProved:    int(r.GetFloat("conjectures_proved")),
				Prover:              r.GetString("prover"),
				ProofStatus:         r.GetString("proof_status"),
				NFTMetadata:         r.Get("nft_metadata"),
			})
		}
		return e.JSON(http.StatusOK, entries)
	})

	// GET /reviews-list — list reviews with nft_metadata (for NFT gallery)
	se.Router.GET("/reviews-list", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("reviews")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type reviewEntry struct {
			ReviewID            string `json:"review_id"`
			ReviewerUsername    string `json:"reviewer_username"`
			PackagesReviewed    int    `json:"packages_reviewed"`
			ConjecturesCompared int    `json:"conjectures_compared"`
			Recommendation      string `json:"recommendation"`
			NFTMetadata         any    `json:"nft_metadata"`
		}

		entries := make([]reviewEntry, 0, len(records))
		for _, r := range records {
			entries = append(entries, reviewEntry{
				ReviewID:            r.GetString("review_id"),
				ReviewerUsername:    r.GetString("reviewer_username"),
				PackagesReviewed:    int(r.GetFloat("packages_reviewed")),
				ConjecturesCompared: int(r.GetFloat("conjectures_compared")),
				Recommendation:      r.GetString("recommendation"),
				NFTMetadata:         r.Get("nft_metadata"),
			})
		}
		return e.JSON(http.StatusOK, entries)
	})

	// POST /conjectures/packages — submit conjectures (simplified: JSON only for PocketBase)
	se.Router.POST("/conjectures/packages", func(e *core.RequestEvent) error {
		var conjectures []struct {
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

		if err := e.BindBody(&conjectures); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		collection, err := app.FindCollectionByNameOrId("conjectures")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		var added []string
		for _, p := range conjectures {
			if p.ID == "" {
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

			if err := app.Save(record); err != nil {
				continue
			}
			added = append(added, p.ID)
		}

		if added == nil {
			added = []string{}
		}

		return e.JSON(http.StatusOK, map[string]any{
			"status":               "accepted",
			"added_conjecture_ids": added,
			"count":                len(added),
		})
	}).Bind(apis.RequireAuth())

	// Serve embedded static files (web UI)
	fileServer := http.FileServer(http.FS(static.Files))
	se.Router.GET("/{path...}", func(e *core.RequestEvent) error {
		fileServer.ServeHTTP(e.Response, e.Request)
		return nil
	})

	// Seed conjectures from filesystem on startup
	seedConjectures(app)
}

// seedConjectures loads conjecture JSON files from the PROBLEMS_DIR directory.
func seedConjectures(app core.App) {
	dir := os.Getenv("PROBLEMS_DIR")
	if dir == "" {
		dir = "problems"
	}

	entries, err := os.ReadDir(dir)
	if err != nil {
		return // no problems dir, skip silently
	}

	collection, err := app.FindCollectionByNameOrId("conjectures")
	if err != nil {
		return
	}

	for _, entry := range entries {
		if entry.IsDir() || filepath.Ext(entry.Name()) != ".json" {
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
