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

		// ── contribution_results ──
		results := core.NewBaseCollection("contribution_results")
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
			"CREATE INDEX idx_contribution_results_conjecture_id ON contribution_results (conjecture_id)",
			"CREATE INDEX idx_contribution_results_username ON contribution_results (username)",
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
			&core.JSONField{Name: "certified_by"},
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

		// ── certificates ──
		certificates := core.NewBaseCollection("certificates")
		certificates.Fields.Add(
			&core.TextField{Name: "certificate_id", Required: true, Max: 200},
			&core.TextField{Name: "certifier_username", Required: true, Max: 200},
			&core.NumberField{Name: "packages_certified", OnlyInt: true},
			&core.NumberField{Name: "conjectures_compared", OnlyInt: true},
			&core.JSONField{Name: "package_rankings"},
			&core.TextField{Name: "recommendation"},
			&core.TextField{Name: "archive_sha256", Max: 100},
			&core.JSONField{Name: "nft_metadata"},
		)
		certificates.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_certificates_certificate_id ON certificates (certificate_id)",
		}
		certificates.ViewRule = types.Pointer("")
		certificates.ListRule = types.Pointer("")
		certificates.CreateRule = types.Pointer("@request.auth.id != ''")
		if err := app.Save(certificates); err != nil {
			return err
		}

		// ── user profile fields ──
		users, err := app.FindCollectionByNameOrId("users")
		if err != nil {
			return err
		}
		users.Fields.Add(
			&core.TextField{Name: "username", Max: 200},
			&core.TextField{Name: "real_name", Max: 200},
			&core.TextField{Name: "affiliation", Max: 300},
		)
		if err := app.Save(users); err != nil {
			return err
		}

		return nil
	}, func(app core.App) error {
		// Rollback: delete collections in reverse dependency order
		for _, name := range []string{"certificates", "contributions", "contribution_results", "conjectures"} {
			c, _ := app.FindCollectionByNameOrId(name)
			if c != nil {
				app.Delete(c)
			}
		}
		return nil
	})
}
