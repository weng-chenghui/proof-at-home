package data

import (
	"os"
	"path/filepath"
	"testing"
)

func TestParseLessonFile_NewmanLemma(t *testing.T) {
	raw, err := os.ReadFile(filepath.Join("..", "..", "..", "examples", "data-repo", "lessons", "newman-lemma", "lesson.md"))
	if err != nil {
		t.Fatal("read newman-lemma/lesson.md:", err)
	}

	l, err := ParseLessonFile(raw)
	if err != nil {
		t.Fatal("ParseLessonFile:", err)
	}

	if l.LessonID != "newman-lemma" {
		t.Errorf("LessonID = %q, want %q", l.LessonID, "newman-lemma")
	}
	if l.Title != "Newman's Lemma: From Local to Global Confluence" {
		t.Errorf("Title = %q", l.Title)
	}
	if !l.Published {
		t.Error("Published should be true")
	}
	if len(l.ConjectureIDs) != 6 {
		t.Errorf("ConjectureIDs len = %d, want 6", len(l.ConjectureIDs))
	}
	if len(l.AIAnnotations) != 3 {
		t.Errorf("AIAnnotations len = %d, want 3", len(l.AIAnnotations))
	}
	if l.Content == "" {
		t.Error("Content should not be empty")
	}
}

func TestParseLessonFile_HowToCreateALesson(t *testing.T) {
	raw, err := os.ReadFile(filepath.Join("..", "..", "..", "examples", "data-repo", "lessons", "how-to-create-a-lesson", "lesson.md"))
	if err != nil {
		t.Fatal("read how-to-create-a-lesson/lesson.md:", err)
	}

	l, err := ParseLessonFile(raw)
	if err != nil {
		t.Fatal("ParseLessonFile:", err)
	}

	if l.LessonID != "how-to-create-a-lesson" {
		t.Errorf("LessonID = %q, want %q", l.LessonID, "how-to-create-a-lesson")
	}
	if !l.Published {
		t.Error("Published should be true")
	}
	if len(l.ConjectureIDs) != 0 {
		t.Errorf("ConjectureIDs len = %d, want 0", len(l.ConjectureIDs))
	}
	if len(l.AIAnnotations) != 3 {
		t.Errorf("AIAnnotations len = %d, want 3", len(l.AIAnnotations))
	}
	if l.Content == "" {
		t.Error("Content should not be empty")
	}
}
