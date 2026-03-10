package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
	"github.com/pocketbase/pocketbase/tools/types"
)

func init() {
	m.Register(func(app core.App) error {
		notes := core.NewBaseCollection("notes")
		notes.Fields.Add(
			&core.TextField{Name: "note_id", Required: true, Max: 200},
			&core.TextField{Name: "lesson_id", Required: true, Max: 200},
			&core.TextField{Name: "content_hash", Max: 200},
			&core.TextField{Name: "anchor_text"},
			&core.NumberField{Name: "line_start"},
			&core.NumberField{Name: "line_end"},
			&core.TextField{Name: "content"},
			&core.TextField{Name: "highlight_color", Max: 20},
			&core.TextField{Name: "user_id", Max: 200},
			&core.TextField{Name: "username", Max: 200},
			&core.TextField{Name: "status", Max: 50},
		)
		notes.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_notes_note_id ON notes (note_id)",
			"CREATE INDEX idx_notes_lesson_id ON notes (lesson_id)",
		}
		notes.ViewRule = types.Pointer("")
		notes.ListRule = types.Pointer("")
		notes.CreateRule = types.Pointer("@request.auth.id != ''")
		notes.UpdateRule = types.Pointer("@request.auth.id != '' && user_id = @request.auth.id")
		notes.DeleteRule = types.Pointer("@request.auth.id != '' && user_id = @request.auth.id")
		if err := app.Save(notes); err != nil {
			return err
		}
		return nil
	}, func(app core.App) error {
		c, _ := app.FindCollectionByNameOrId("notes")
		if c != nil {
			app.Delete(c)
		}
		return nil
	})
}
