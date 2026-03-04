package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
	"github.com/pocketbase/pocketbase/tools/types"
)

func init() {
	m.Register(func(app core.App) error {
		visualizations := core.NewBaseCollection("visualizations")
		visualizations.Fields.Add(
			&core.TextField{Name: "visualization_id", Required: true, Max: 200},
			&core.TextField{Name: "author_username", Required: true, Max: 200},
			&core.TextField{Name: "conjecture_id", Max: 200},
			&core.TextField{Name: "domain", Max: 200},
			&core.TextField{Name: "title"},
			&core.TextField{Name: "summary"},
			&core.JSONField{Name: "viz_json"},
			&core.NumberField{Name: "cost_usd"},
			&core.TextField{Name: "strategy_used", Max: 200},
			&core.JSONField{Name: "nft_metadata"},
		)
		visualizations.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_visualizations_visualization_id ON visualizations (visualization_id)",
		}
		visualizations.ViewRule = types.Pointer("")
		visualizations.ListRule = types.Pointer("")
		visualizations.CreateRule = types.Pointer("@request.auth.id != ''")
		visualizations.UpdateRule = types.Pointer("@request.auth.id != ''")
		return app.Save(visualizations)
	}, func(app core.App) error {
		c, _ := app.FindCollectionByNameOrId("visualizations")
		if c != nil {
			app.Delete(c)
		}
		return nil
	})
}
