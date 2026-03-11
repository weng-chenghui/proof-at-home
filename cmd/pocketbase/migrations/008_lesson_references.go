package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
)

func init() {
	m.Register(func(app core.App) error {
		lessons, err := app.FindCollectionByNameOrId("lessons")
		if err != nil {
			return err
		}
		// Add a JSON field for CSL-JSON compatible references array.
		lessons.Fields.Add(
			&core.JSONField{Name: "references", MaxSize: 500000},
		)
		return app.Save(lessons)
	}, func(app core.App) error {
		lessons, err := app.FindCollectionByNameOrId("lessons")
		if err != nil {
			return err
		}
		lessons.Fields.RemoveByName("references")
		return app.Save(lessons)
	})
}
