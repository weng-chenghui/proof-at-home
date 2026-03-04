package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
)

func init() {
	m.Register(func(app core.App) error {
		// Add domain, title, summary fields to expositions collection
		expositions, err := app.FindCollectionByNameOrId("expositions")
		if err != nil {
			return err
		}

		expositions.Fields.Add(
			&core.TextField{Name: "domain", Max: 200},
			&core.TextField{Name: "title"},
			&core.TextField{Name: "summary"},
		)
		if err := app.Save(expositions); err != nil {
			return err
		}

		// Drop the visualizations collection (data migrated at rebuild time)
		vizCollection, _ := app.FindCollectionByNameOrId("visualizations")
		if vizCollection != nil {
			if err := app.Delete(vizCollection); err != nil {
				return err
			}
		}

		return nil
	}, func(app core.App) error {
		// Down: remove fields from expositions, recreate visualizations
		// Not implementing full rollback — PocketBase handles this at rebuild
		return nil
	})
}
