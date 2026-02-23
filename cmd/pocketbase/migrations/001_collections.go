package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
	"github.com/pocketbase/pocketbase/tools/types"
)

func init() {
	m.Register(func(app core.App) error {
		// ── conjectures ──
		conjectures := core.NewBaseCollection("conjectures")
		conjectures.Fields.Add(
			&core.TextField{Name: "conjecture_id", Required: true, Max: 200},
			&core.TextField{Name: "title", Max: 500},
			&core.SelectField{Name: "difficulty", Values: []string{"easy", "medium", "hard"}},
			&core.TextField{Name: "prover", Max: 100},
			&core.SelectField{
				Name:     "status",
				Required: true,
				Values:   []string{"open", "proved"},
			},
			&core.TextField{Name: "preamble"},
			&core.TextField{Name: "lemma_statement"},
			&core.JSONField{Name: "hints"},
			&core.TextField{Name: "skeleton"},
			&core.JSONField{Name: "dependencies"},
		)
		conjectures.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_conjectures_conjecture_id ON conjectures (conjecture_id)",
		}
		// Public read, authenticated write
		conjectures.ViewRule = types.Pointer("")
		conjectures.ListRule = types.Pointer("")
		conjectures.CreateRule = types.Pointer("@request.auth.id != ''")
		conjectures.UpdateRule = types.Pointer("@request.auth.id != ''")
		if err := app.Save(conjectures); err != nil {
			return err
		}

		// ── certificates ──
		results := core.NewBaseCollection("certificates")
		results.Fields.Add(
			&core.TextField{Name: "conjecture_id", Required: true, Max: 200},
			&core.TextField{Name: "username", Required: true, Max: 200},
			&core.BoolField{Name: "success"},
			&core.TextField{Name: "proof_script"},
			&core.NumberField{Name: "cost_usd"},
			&core.NumberField{Name: "attempts", OnlyInt: true},
			&core.TextField{Name: "error_output"},
		)
		results.Indexes = types.JSONArray[string]{
			"CREATE INDEX idx_certificates_conjecture_id ON certificates (conjecture_id)",
			"CREATE INDEX idx_certificates_username ON certificates (username)",
		}
		results.ViewRule = types.Pointer("")
		results.ListRule = types.Pointer("")
		results.CreateRule = types.Pointer("@request.auth.id != ''")
		if err := app.Save(results); err != nil {
			return err
		}

		// ── contributions ──
		contributions := core.NewBaseCollection("contributions")
		contributions.Fields.Add(
			&core.TextField{Name: "contribution_id", Required: true, Max: 200},
			&core.TextField{Name: "username", Required: true, Max: 200},
			&core.NumberField{Name: "conjectures_attempted", OnlyInt: true},
			&core.NumberField{Name: "conjectures_proved", OnlyInt: true},
			&core.NumberField{Name: "cost_usd"},
			&core.TextField{Name: "archive_sha256", Max: 100},
			&core.JSONField{Name: "nft_metadata"},
			&core.TextField{Name: "prover", Max: 100},
			&core.JSONField{Name: "conjecture_ids"},
			&core.FileField{
				Name:      "archive",
				MaxSelect: 1,
				MaxSize:   100 * 1024 * 1024, // 100MB
				MimeTypes: []string{"application/gzip", "application/x-gzip", "application/octet-stream"},
			},
			&core.TextField{Name: "proof_status", Max: 100},
			&core.JSONField{Name: "reviewed_by"},
		)
		contributions.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_contributions_contribution_id ON contributions (contribution_id)",
		}
		contributions.ViewRule = types.Pointer("")
		contributions.ListRule = types.Pointer("")
		contributions.CreateRule = types.Pointer("@request.auth.id != ''")
		contributions.UpdateRule = types.Pointer("@request.auth.id != ''")
		if err := app.Save(contributions); err != nil {
			return err
		}

		// ── reviews ──
		reviews := core.NewBaseCollection("reviews")
		reviews.Fields.Add(
			&core.TextField{Name: "review_id", Required: true, Max: 200},
			&core.TextField{Name: "reviewer_username", Required: true, Max: 200},
			&core.NumberField{Name: "packages_reviewed", OnlyInt: true},
			&core.NumberField{Name: "conjectures_compared", OnlyInt: true},
			&core.JSONField{Name: "package_rankings"},
			&core.TextField{Name: "recommendation"},
			&core.TextField{Name: "archive_sha256", Max: 100},
			&core.JSONField{Name: "nft_metadata"},
		)
		reviews.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_reviews_review_id ON reviews (review_id)",
		}
		reviews.ViewRule = types.Pointer("")
		reviews.ListRule = types.Pointer("")
		reviews.CreateRule = types.Pointer("@request.auth.id != ''")
		if err := app.Save(reviews); err != nil {
			return err
		}

		return nil
	}, func(app core.App) error {
		// Rollback: delete collections in reverse dependency order
		for _, name := range []string{"reviews", "contributions", "certificates", "conjectures"} {
			c, _ := app.FindCollectionByNameOrId(name)
			if c != nil {
				app.Delete(c)
			}
		}
		return nil
	})
}
