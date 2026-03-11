package handlers

import (
	"encoding/json"
	"log"
	"net/http"

	"github.com/google/uuid"
	"github.com/proof-at-home/server/src/server/data"
	authmw "github.com/proof-at-home/server/src/server/middleware"
)

// NoteStore defines the subset of store methods needed by NoteHandler.
type NoteStore interface {
	ListNotes(lessonID string) []data.Note
	ListAllNotes() []data.Note
	GetNote(noteID string) (data.Note, bool)
	CreateNote(note data.Note) error
	UpdateNote(note data.Note) error
	DeleteNote(noteID string) error
}

// NoteGitExporter can export notes to a git branch.
type NoteGitExporter interface {
	ExportNotesToGit(notes []data.Note) error
}

// NoteHandler handles CRUD operations for lesson notes and highlights.
type NoteHandler struct {
	Store    NoteStore
	GitStore NoteGitExporter
}

// exportNotes exports all notes to git in the background.
func (h *NoteHandler) exportNotes() {
	if h.GitStore == nil {
		return
	}
	go func() {
		notes := h.Store.ListAllNotes()
		if len(notes) == 0 {
			return
		}
		if err := h.GitStore.ExportNotesToGit(notes); err != nil {
			log.Printf("notes git export failed: %v", err)
		}
	}()
}

// ListNotes returns all notes for a lesson. GET /lessons/{id}/notes
func (h *NoteHandler) ListNotes(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	lessonID := r.PathValue("id")

	notes := h.Store.ListNotes(lessonID)
	if notes == nil {
		notes = []data.Note{}
	}
	json.NewEncoder(w).Encode(notes)
}

// CreateNote creates a new note for a lesson. POST /lessons/{id}/notes
func (h *NoteHandler) CreateNote(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	lessonID := r.PathValue("id")

	var note data.Note
	if err := json.NewDecoder(r.Body).Decode(&note); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	note.LessonID = lessonID

	if note.NoteID == "" {
		note.NoteID = uuid.New().String()
	}
	if note.Status == "" {
		note.Status = "active"
	}

	// Extract user info from auth context; fall back to body values
	if userID, _ := r.Context().Value(authmw.UserSubKey).(string); userID != "" {
		note.UserID = userID
	}
	if username, _ := r.Context().Value(authmw.UserNicknameKey).(string); username != "" {
		note.Username = username
	}

	if err := h.Store.CreateNote(note); err != nil {
		http.Error(w, `{"error":"failed to create note: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	// Re-read the note to get server-generated timestamps
	created, ok := h.Store.GetNote(note.NoteID)
	if ok {
		note = created
	}

	h.exportNotes()
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(note)
}

// UpdateNote updates an existing note. PATCH /notes/{noteId}
func (h *NoteHandler) UpdateNote(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	noteID := r.PathValue("noteId")

	existing, ok := h.Store.GetNote(noteID)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}

	userID, _ := r.Context().Value(authmw.UserSubKey).(string)
	if userID != "" && existing.UserID != userID {
		http.Error(w, `{"error":"forbidden"}`, http.StatusForbidden)
		return
	}

	var patch data.Note
	if err := json.NewDecoder(r.Body).Decode(&patch); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	// Only allow updating content, highlight_color, and status
	if patch.Content != "" {
		existing.Content = patch.Content
	}
	if patch.HighlightColor != "" {
		existing.HighlightColor = patch.HighlightColor
	}
	if patch.Status != "" {
		existing.Status = patch.Status
	}

	if err := h.Store.UpdateNote(existing); err != nil {
		http.Error(w, `{"error":"failed to update note: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	updated, ok := h.Store.GetNote(noteID)
	if ok {
		existing = updated
	}

	h.exportNotes()
	json.NewEncoder(w).Encode(existing)
}

// DeleteNote deletes a note. DELETE /notes/{noteId}
func (h *NoteHandler) DeleteNote(w http.ResponseWriter, r *http.Request) {
	noteID := r.PathValue("noteId")

	existing, ok := h.Store.GetNote(noteID)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}

	userID, _ := r.Context().Value(authmw.UserSubKey).(string)
	if userID != "" && existing.UserID != userID {
		http.Error(w, `{"error":"forbidden"}`, http.StatusForbidden)
		return
	}

	if err := h.Store.DeleteNote(noteID); err != nil {
		http.Error(w, `{"error":"failed to delete note: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	h.exportNotes()
	w.WriteHeader(http.StatusNoContent)
}
