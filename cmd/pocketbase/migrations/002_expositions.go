package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
	"github.com/pocketbase/pocketbase/tools/types"
)

func init() {
	m.Register(func(app core.App) error {
		expositions := core.NewBaseCollection("expositions")
		expositions.Fields.Add(
			&core.TextField{Name: "exposition_id", Required: true, Max: 200},
			&core.TextField{Name: "author_username", Required: true, Max: 200},
			&core.TextField{Name: "contribution_id", Max: 200},
			&core.TextField{Name: "conjecture_id", Max: 200},
			&core.TextField{Name: "prover", Max: 100},
			&core.TextField{Name: "proof_script"},
			&core.TextField{Name: "exposition_text"},
			&core.NumberField{Name: "cost_usd"},
			&core.TextField{Name: "strategy_used", Max: 200},
			&core.JSONField{Name: "nft_metadata"},
		)
		expositions.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_expositions_exposition_id ON expositions (exposition_id)",
		}
		expositions.ViewRule = types.Pointer("")
		expositions.ListRule = types.Pointer("")
		expositions.CreateRule = types.Pointer("@request.auth.id != ''")
		expositions.UpdateRule = types.Pointer("@request.auth.id != ''")
		return app.Save(expositions)
	}, func(app core.App) error {
		c, _ := app.FindCollectionByNameOrId("expositions")
		if c != nil {
			app.Delete(c)
		}
		return nil
	})
}
