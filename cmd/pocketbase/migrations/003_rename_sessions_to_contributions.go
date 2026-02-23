package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
	"github.com/pocketbase/pocketbase/tools/types"
)

func init() {
	m.Register(func(app core.App) error {
		collection, err := app.FindCollectionByNameOrId("sessions")
		if err != nil {
			return err
		}

		// Rename collection
		collection.Name = "contributions"

		// Rename session_id field to contribution_id
		if field := collection.Fields.GetByName("session_id"); field != nil {
			field.SetName("contribution_id")
		}

		// Update index
		collection.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_contributions_contribution_id ON contributions (contribution_id)",
		}

		return app.Save(collection)
	}, func(app core.App) error {
		collection, err := app.FindCollectionByNameOrId("contributions")
		if err != nil {
			return err
		}

		collection.Name = "sessions"

		if field := collection.Fields.GetByName("contribution_id"); field != nil {
			field.SetName("session_id")
		}

		collection.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_sessions_session_id ON sessions (session_id)",
		}

		return app.Save(collection)
	})
}
