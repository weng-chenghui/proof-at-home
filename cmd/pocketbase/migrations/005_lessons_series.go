package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
	"github.com/pocketbase/pocketbase/tools/types"
)

func init() {
	m.Register(func(app core.App) error {
		// ── lessons ──
		lessons := core.NewBaseCollection("lessons")
		lessons.Fields.Add(
			&core.TextField{Name: "lesson_id", Required: true, Max: 200},
			&core.TextField{Name: "author_username", Max: 200},
			&core.TextField{Name: "title", Max: 500},
			&core.TextField{Name: "topic", Max: 200},
			&core.TextField{Name: "difficulty", Max: 100},
			&core.TextField{Name: "description"},
			&core.TextField{Name: "prerequisites"},
			&core.JSONField{Name: "conjecture_ids"},
			&core.BoolField{Name: "published"},
			&core.TextField{Name: "content"},
			&core.JSONField{Name: "ai_annotations"},
		)
		lessons.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_lessons_lesson_id ON lessons (lesson_id)",
		}
		lessons.ViewRule = types.Pointer("")
		lessons.ListRule = types.Pointer("")
		lessons.CreateRule = types.Pointer("@request.auth.id != ''")
		lessons.UpdateRule = types.Pointer("@request.auth.id != ''")
		if err := app.Save(lessons); err != nil {
			return err
		}

		// ── series ──
		series := core.NewBaseCollection("series")
		series.Fields.Add(
			&core.TextField{Name: "series_id", Required: true, Max: 200},
			&core.TextField{Name: "title", Max: 500},
			&core.TextField{Name: "author_username", Max: 200},
			&core.TextField{Name: "difficulty", Max: 100},
			&core.TextField{Name: "description"},
			&core.JSONField{Name: "lesson_ids"},
			&core.BoolField{Name: "published"},
			&core.TextField{Name: "content"},
		)
		series.Indexes = types.JSONArray[string]{
			"CREATE UNIQUE INDEX idx_series_series_id ON series (series_id)",
		}
		series.ViewRule = types.Pointer("")
		series.ListRule = types.Pointer("")
		series.CreateRule = types.Pointer("@request.auth.id != ''")
		series.UpdateRule = types.Pointer("@request.auth.id != ''")
		if err := app.Save(series); err != nil {
			return err
		}

		return nil
	}, func(app core.App) error {
		for _, name := range []string{"series", "lessons"} {
			c, _ := app.FindCollectionByNameOrId(name)
			if c != nil {
				app.Delete(c)
			}
		}
		return nil
	})
}
