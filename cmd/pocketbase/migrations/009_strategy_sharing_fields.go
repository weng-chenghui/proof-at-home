package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
)

func init() {
	m.Register(func(app core.App) error {
		strategies, err := app.FindCollectionByNameOrId("strategies")
		if err != nil {
			return err
		}
		strategies.Fields.Add(
			&core.TextField{Name: "version", Max: 100},
			&core.TextField{Name: "author", Max: 200},
			&core.TextField{Name: "license", Max: 100},
			&core.TextField{Name: "source", Max: 500},
		)
		return app.Save(strategies)
	}, func(app core.App) error {
		strategies, err := app.FindCollectionByNameOrId("strategies")
		if err != nil {
			return err
		}
		strategies.Fields.RemoveByName("version")
		strategies.Fields.RemoveByName("author")
		strategies.Fields.RemoveByName("license")
		strategies.Fields.RemoveByName("source")
		return app.Save(strategies)
	})
}
