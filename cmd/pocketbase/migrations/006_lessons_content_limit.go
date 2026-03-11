package migrations

import (
	"github.com/pocketbase/pocketbase/core"
	m "github.com/pocketbase/pocketbase/migrations"
)

func init() {
	m.Register(func(app core.App) error {
		// Replace TextField with EditorField for content.
		// TextField defaults Max to 5000 chars which is too small for
		// markdown articles. EditorField defaults to 5 MB.
		for _, name := range []string{"lessons", "series"} {
			c, err := app.FindCollectionByNameOrId(name)
			if err != nil {
				return err
			}
			c.Fields.RemoveByName("content")
			c.Fields.Add(&core.EditorField{Name: "content"})
			if err := app.Save(c); err != nil {
				return err
			}
		}
		return nil
	}, func(app core.App) error {
		for _, name := range []string{"lessons", "series"} {
			c, err := app.FindCollectionByNameOrId(name)
			if err != nil {
				return err
			}
			c.Fields.RemoveByName("content")
			c.Fields.Add(&core.TextField{Name: "content"})
			if err := app.Save(c); err != nil {
				return err
			}
		}
		return nil
	})
}
