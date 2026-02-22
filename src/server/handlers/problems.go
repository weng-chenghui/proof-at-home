package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/go-chi/chi/v5"
	"github.com/proof-at-home/server/src/server/store"
)

type ProblemHandler struct {
	Store store.Store
}

func (h *ProblemHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	summaries := h.Store.ListProblems()
	json.NewEncoder(w).Encode(summaries)
}

func (h *ProblemHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := chi.URLParam(r, "id")
	p, ok := h.Store.GetProblem(id)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(p)
}
