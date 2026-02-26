package hooks

import (
	"log/slog"
	"sync/atomic"

	"github.com/pocketbase/pocketbase/core"
)

// IsRebuilding is set to true during cache rebuilds to prevent hooks from
// triggering git writes for records being replayed from the filesystem.
var IsRebuilding atomic.Bool

// Register adds all business logic hooks to the PocketBase app.
func Register(app core.App) {
	// When a successful proof is created, mark the conjecture as "proved"
	app.OnRecordAfterCreateSuccess("proofs").BindFunc(func(e *core.RecordEvent) error {
		if IsRebuilding.Load() {
			return e.Next()
		}

		if !e.Record.GetBool("success") {
			return e.Next()
		}

		conjectureID := e.Record.GetString("conjecture_id")
		if conjectureID == "" {
			return e.Next()
		}

		// Find the conjecture by its conjecture_id field
		conjecture, err := e.App.FindFirstRecordByFilter("conjectures", "conjecture_id = {:pid}", map[string]any{
			"pid": conjectureID,
		})
		if err != nil {
			slog.Warn("Could not find conjecture to update status",
				"conjecture_id", conjectureID, "error", err)
			return e.Next()
		}

		conjecture.Set("status", "proved")
		if err := e.App.Save(conjecture); err != nil {
			slog.Error("Failed to update conjecture status to proved",
				"conjecture_id", conjectureID, "error", err)
		}

		return e.Next()
	})

	// When a certificate is created, update certified_by on affected contributions
	app.OnRecordAfterCreateSuccess("certificates").BindFunc(func(e *core.RecordEvent) error {
		if IsRebuilding.Load() {
			return e.Next()
		}

		certifier := e.Record.GetString("certifier_username")
		rankings := e.Record.Get("package_rankings")

		// package_rankings is a JSON array of {contributor_contribution_id, rank, overall_score}
		rankingsList, ok := rankings.([]any)
		if !ok || len(rankingsList) == 0 {
			return e.Next()
		}

		for _, item := range rankingsList {
			ranking, ok := item.(map[string]any)
			if !ok {
				continue
			}

			contributionID, _ := ranking["contributor_contribution_id"].(string)
			if contributionID == "" {
				continue
			}

			contribution, err := e.App.FindFirstRecordByFilter("contributions", "contribution_id = {:cid}", map[string]any{
				"cid": contributionID,
			})
			if err != nil {
				slog.Warn("Could not find contribution to update certified_by",
					"contribution_id", contributionID, "error", err)
				continue
			}

			// Get current certified_by list and add certifier if not present
			certifiedBy := contribution.Get("certified_by")
			certifiers, _ := certifiedBy.([]any)

			found := false
			for _, r := range certifiers {
				if r == certifier {
					found = true
					break
				}
			}

			if !found {
				certifiers = append(certifiers, certifier)
				contribution.Set("certified_by", certifiers)
				if err := e.App.Save(contribution); err != nil {
					slog.Error("Failed to update contribution certified_by",
						"contribution_id", contributionID, "error", err)
				}
			}
		}

		return e.Next()
	})
}
