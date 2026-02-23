package hooks

import (
	"log/slog"

	"github.com/pocketbase/pocketbase/core"
)

// Register adds all business logic hooks to the PocketBase app.
func Register(app core.App) {
	// When a successful proof result is created, mark the conjecture as "proved"
	app.OnRecordAfterCreateSuccess("certificates").BindFunc(func(e *core.RecordEvent) error {
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

	// When a review is created, update reviewed_by on affected contributions
	app.OnRecordAfterCreateSuccess("reviews").BindFunc(func(e *core.RecordEvent) error {
		reviewer := e.Record.GetString("reviewer_username")
		rankings := e.Record.Get("package_rankings")

		// package_rankings is a JSON array of {prover_contribution_id, rank, overall_score}
		rankingsList, ok := rankings.([]any)
		if !ok || len(rankingsList) == 0 {
			return e.Next()
		}

		for _, item := range rankingsList {
			ranking, ok := item.(map[string]any)
			if !ok {
				continue
			}

			contributionID, _ := ranking["prover_contribution_id"].(string)
			if contributionID == "" {
				continue
			}

			contribution, err := e.App.FindFirstRecordByFilter("contributions", "contribution_id = {:cid}", map[string]any{
				"cid": contributionID,
			})
			if err != nil {
				slog.Warn("Could not find contribution to update reviewed_by",
					"contribution_id", contributionID, "error", err)
				continue
			}

			// Get current reviewed_by list and add reviewer if not present
			reviewedBy := contribution.Get("reviewed_by")
			reviewers, _ := reviewedBy.([]any)

			found := false
			for _, r := range reviewers {
				if r == reviewer {
					found = true
					break
				}
			}

			if !found {
				reviewers = append(reviewers, reviewer)
				contribution.Set("reviewed_by", reviewers)
				if err := e.App.Save(contribution); err != nil {
					slog.Error("Failed to update contribution reviewed_by",
						"contribution_id", contributionID, "error", err)
				}
			}
		}

		return e.Next()
	})
}
