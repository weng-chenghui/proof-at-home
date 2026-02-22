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
	// GET /problems — list all problems
	se.Router.GET("/problems", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("problems")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type problemSummary struct {
			ID             string `json:"id"`
			Title          string `json:"title"`
			Difficulty     string `json:"difficulty"`
			ProofAssistant string `json:"proof_assistant"`
			Status         string `json:"status"`
		}

		summaries := make([]problemSummary, 0, len(records))
		for _, r := range records {
			summaries = append(summaries, problemSummary{
				ID:             r.GetString("problem_id"),
				Title:          r.GetString("title"),
				Difficulty:     r.GetString("difficulty"),
				ProofAssistant: r.GetString("proof_assistant"),
				Status:         r.GetString("status"),
			})
		}
		return e.JSON(http.StatusOK, summaries)
	})

	// GET /problems/{id} — get specific problem
	se.Router.GET("/problems/{id}", func(e *core.RequestEvent) error {
		id := e.Request.PathValue("id")
		record, err := app.FindFirstRecordByFilter("problems", "problem_id = {:pid}", map[string]any{
			"pid": id,
		})
		if err != nil {
			return e.JSON(http.StatusNotFound, map[string]string{"error": "not found"})
		}

		problem := map[string]any{
			"id":              record.GetString("problem_id"),
			"title":           record.GetString("title"),
			"difficulty":      record.GetString("difficulty"),
			"proof_assistant": record.GetString("proof_assistant"),
			"status":          record.GetString("status"),
			"preamble":        record.GetString("preamble"),
			"lemma_statement": record.GetString("lemma_statement"),
			"hints":           record.Get("hints"),
			"skeleton":        record.GetString("skeleton"),
			"dependencies":    record.Get("dependencies"),
		}
		return e.JSON(http.StatusOK, problem)
	})

	// POST /results — submit individual proof result
	se.Router.POST("/results", func(e *core.RequestEvent) error {
		var body struct {
			ProblemID   string  `json:"problem_id"`
			Username    string  `json:"username"`
			Success     bool    `json:"success"`
			ProofScript string  `json:"proof_script"`
			CostUSD     float64 `json:"cost_usd"`
			Attempts    int     `json:"attempts"`
			ErrorOutput string  `json:"error_output"`
		}
		if err := e.BindBody(&body); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		collection, err := app.FindCollectionByNameOrId("proof_results")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		record := core.NewRecord(collection)
		record.Set("problem_id", body.ProblemID)
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

	// POST /results/batch — submit session summary
	se.Router.POST("/results/batch", func(e *core.RequestEvent) error {
		var body struct {
			Username          string  `json:"username"`
			SessionID         string  `json:"session_id"`
			ProblemsAttempted int     `json:"problems_attempted"`
			ProblemsProved    int     `json:"problems_proved"`
			TotalCostUSD      float64 `json:"total_cost_usd"`
			ArchiveSHA256     string  `json:"archive_sha256"`
			NFTMetadata       any     `json:"nft_metadata"`
			ProofAssistant    string  `json:"proof_assistant"`
			ProblemIDs        []string `json:"problem_ids"`
			ArchivePath       string  `json:"archive_path"`
			ProofStatus       string  `json:"proof_status"`
			ReviewedBy        []string `json:"reviewed_by"`
		}
		if err := e.BindBody(&body); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		collection, err := app.FindCollectionByNameOrId("sessions")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		record := core.NewRecord(collection)
		record.Set("session_id", body.SessionID)
		record.Set("username", body.Username)
		record.Set("problems_attempted", body.ProblemsAttempted)
		record.Set("problems_proved", body.ProblemsProved)
		record.Set("cost_usd", body.TotalCostUSD)
		record.Set("archive_sha256", body.ArchiveSHA256)
		record.Set("nft_metadata", body.NFTMetadata)
		record.Set("proof_assistant", body.ProofAssistant)
		record.Set("problem_ids", body.ProblemIDs)
		record.Set("proof_status", body.ProofStatus)
		record.Set("reviewed_by", body.ReviewedBy)

		if err := app.Save(record); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{"status": "accepted"})
	})

	// GET /review-packages — list review packages
	se.Router.GET("/review-packages", func(e *core.RequestEvent) error {
		records, err := app.FindAllRecords("sessions")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		type reviewPkg struct {
			ProverSessionID string   `json:"prover_session_id"`
			ProverUsername  string   `json:"prover_username"`
			ProofAssistant  string   `json:"proof_assistant"`
			ProblemIDs      []string `json:"problem_ids"`
			ArchiveURL      string   `json:"archive_url"`
			ArchiveSHA256   string   `json:"archive_sha256"`
			ProofStatus     string   `json:"proof_status,omitempty"`
			ReviewedBy      []string `json:"reviewed_by,omitempty"`
		}

		packages := make([]reviewPkg, 0, len(records))
		for _, r := range records {
			sessionID := r.GetString("session_id")

			proofAssistant := r.GetString("proof_assistant")
			if proofAssistant == "" {
				proofAssistant = "rocq"
			}

			// Get problem_ids from JSON field
			var problemIDs []string
			if raw := r.Get("problem_ids"); raw != nil {
				if list, ok := raw.([]any); ok {
					for _, v := range list {
						if s, ok := v.(string); ok {
							problemIDs = append(problemIDs, s)
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
				ProverSessionID: sessionID,
				ProverUsername:  r.GetString("username"),
				ProofAssistant:  proofAssistant,
				ProblemIDs:      problemIDs,
				ArchiveURL:      "/review-packages/" + sessionID + "/archive",
				ArchiveSHA256:   r.GetString("archive_sha256"),
				ProofStatus:     r.GetString("proof_status"),
				ReviewedBy:      reviewedBy,
			})
		}
		return e.JSON(http.StatusOK, packages)
	})

	// GET /review-packages/{sessionID}/archive — download archive
	se.Router.GET("/review-packages/{sessionID}/archive", func(e *core.RequestEvent) error {
		sessionID := e.Request.PathValue("sessionID")

		record, err := app.FindFirstRecordByFilter("sessions", "session_id = {:sid}", map[string]any{
			"sid": sessionID,
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
			ReviewerUsername string `json:"reviewer_username"`
			ReviewID         string `json:"review_id"`
			PackagesReviewed int    `json:"packages_reviewed"`
			ProblemsCompared int    `json:"problems_compared"`
			PackageRankings  []any  `json:"package_rankings"`
			Recommendation   string `json:"recommendation"`
			ArchiveSHA256    string `json:"archive_sha256"`
			NFTMetadata      any    `json:"nft_metadata"`
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
		record.Set("problems_compared", body.ProblemsCompared)
		record.Set("package_rankings", body.PackageRankings)
		record.Set("recommendation", body.Recommendation)
		record.Set("archive_sha256", body.ArchiveSHA256)
		record.Set("nft_metadata", body.NFTMetadata)

		if err := app.Save(record); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": err.Error()})
		}

		return e.JSON(http.StatusCreated, map[string]string{"status": "accepted"})
	})

	// POST /problems/packages — submit problems (simplified: JSON only for PocketBase)
	se.Router.POST("/problems/packages", func(e *core.RequestEvent) error {
		var problems []struct {
			ID             string          `json:"id"`
			Title          string          `json:"title"`
			Difficulty     string          `json:"difficulty"`
			ProofAssistant string          `json:"proof_assistant"`
			Status         string          `json:"status"`
			Preamble       string          `json:"preamble"`
			LemmaStatement string          `json:"lemma_statement"`
			Hints          json.RawMessage `json:"hints"`
			Skeleton       string          `json:"skeleton"`
			Dependencies   json.RawMessage `json:"dependencies"`
		}

		if err := e.BindBody(&problems); err != nil {
			return e.JSON(http.StatusBadRequest, map[string]string{"error": "invalid JSON"})
		}

		collection, err := app.FindCollectionByNameOrId("problems")
		if err != nil {
			return e.JSON(http.StatusInternalServerError, map[string]string{"error": err.Error()})
		}

		var added []string
		for _, p := range problems {
			if p.ID == "" {
				continue
			}

			// Skip if already exists
			existing, _ := app.FindFirstRecordByFilter("problems", "problem_id = {:pid}", map[string]any{
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
			record.Set("problem_id", p.ID)
			record.Set("title", p.Title)
			record.Set("difficulty", p.Difficulty)
			record.Set("proof_assistant", p.ProofAssistant)
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
			"status":           "accepted",
			"added_problem_ids": added,
			"count":            len(added),
		})
	}).Bind(apis.RequireAuth())

	// Serve embedded static files (web UI)
	fileServer := http.FileServer(http.FS(static.Files))
	se.Router.GET("/{path...}", func(e *core.RequestEvent) error {
		fileServer.ServeHTTP(e.Response, e.Request)
		return nil
	})

	// Seed problems from filesystem on startup
	seedProblems(app)
}

// seedProblems loads problem JSON files from the PROBLEMS_DIR directory.
func seedProblems(app core.App) {
	dir := os.Getenv("PROBLEMS_DIR")
	if dir == "" {
		dir = "problems"
	}

	entries, err := os.ReadDir(dir)
	if err != nil {
		return // no problems dir, skip silently
	}

	collection, err := app.FindCollectionByNameOrId("problems")
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
			ProofAssistant string          `json:"proof_assistant"`
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
		existing, _ := app.FindFirstRecordByFilter("problems", "problem_id = {:pid}", map[string]any{
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
		record.Set("problem_id", p.ID)
		record.Set("title", p.Title)
		record.Set("difficulty", p.Difficulty)
		record.Set("proof_assistant", p.ProofAssistant)
		record.Set("status", status)
		record.Set("preamble", p.Preamble)
		record.Set("lemma_statement", p.LemmaStatement)
		record.Set("hints", p.Hints)
		record.Set("skeleton", p.Skeleton)
		record.Set("dependencies", p.Dependencies)

		app.Save(record)
	}
}
