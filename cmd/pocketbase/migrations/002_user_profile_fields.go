package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
)

func init() {
	m.Register(func(app core.App) error {
		users, err := app.FindCollectionByNameOrId("users")
		if err != nil {
			return err
		}

		users.Fields.Add(
			&core.TextField{Name: "username", Max: 200},
			&core.TextField{Name: "real_name", Max: 200},
			&core.TextField{Name: "affiliation", Max: 300},
		)

		return app.Save(users)
	}, func(app core.App) error {
		users, err := app.FindCollectionByNameOrId("users")
		if err != nil {
			return err
		}

		users.Fields.RemoveByName("username")
		users.Fields.RemoveByName("real_name")
		users.Fields.RemoveByName("affiliation")

		return app.Save(users)
	})
}
