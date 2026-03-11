package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
	"github.com/proof-at-home/server/src/server/store/gitstore"
)

type LessonHandler struct {
	Store    store.Store
	GitStore *gitstore.GitStore
}

// List returns all lessons, with optional topic and difficulty filters. GET /lessons
func (h *LessonHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	lessons := h.Store.ListLessons()
	if lessons == nil {
		lessons = []data.Lesson{}
	}

	topic := r.URL.Query().Get("topic")
	difficulty := r.URL.Query().Get("difficulty")

	if topic != "" || difficulty != "" {
		var filtered []data.Lesson
		for _, l := range lessons {
			if topic != "" && l.Topic != topic {
				continue
			}
			if difficulty != "" && l.Difficulty != difficulty {
				continue
			}
			filtered = append(filtered, l)
		}
		if filtered == nil {
			filtered = []data.Lesson{}
		}
		json.NewEncoder(w).Encode(filtered)
		return
	}

	json.NewEncoder(w).Encode(lessons)
}

// Get returns a single lesson by ID, including credits and staleness. GET /lessons/{id}
func (h *LessonHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	l, ok := h.Store.GetLesson(id)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}

	// Compute edition staleness: compare branch HEAD with latest edition commit
	if l.Credits != nil && h.GitStore != nil {
		branch := "lesson/" + id
		branchHead := h.GitStore.BranchHeadSHA(branch)
		if branchHead != "" && len(l.Credits.Edition.History) > 0 {
			lastEditionCommit := l.Credits.Edition.History[len(l.Credits.Edition.History)-1].Commit
			l.EditionStale = branchHead != lastEditionCommit
		}
	}

	json.NewEncoder(w).Encode(l)
}

// Create creates a lesson via GitStore. POST /lessons
func (h *LessonHandler) Create(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var lesson data.Lesson
	if err := json.NewDecoder(r.Body).Decode(&lesson); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	if lesson.LessonID == "" || lesson.Title == "" || lesson.AuthorUsername == "" {
		http.Error(w, `{"error":"lesson_id, title, and author_username are required"}`, http.StatusBadRequest)
		return
	}

	commitSHA, err := h.GitStore.AddLesson(lesson)
	if err != nil {
		http.Error(w, `{"error":"failed to create lesson: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "accepted",
	})
}

// EditionBump increments the edition for a lesson. POST /lessons/{id}/edition-bump
func (h *LessonHandler) EditionBump(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var body struct {
		Summary string `json:"summary"`
	}
	if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}
	if body.Summary == "" {
		http.Error(w, `{"error":"summary is required"}`, http.StatusBadRequest)
		return
	}

	commitSHA, err := h.GitStore.EditionBump("lesson", id, body.Summary)
	if err != nil {
		http.Error(w, `{"error":"failed to bump edition: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "bumped",
	})
}

// Update updates a lesson via GitStore. PATCH /lessons/{id}
func (h *LessonHandler) Update(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var lesson data.Lesson
	if err := json.NewDecoder(r.Body).Decode(&lesson); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	lesson.LessonID = id

	commitSHA, err := h.GitStore.UpdateLesson(id, lesson)
	if err != nil {
		http.Error(w, `{"error":"failed to update lesson: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "accepted",
	})
}
