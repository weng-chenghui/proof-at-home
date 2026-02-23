package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/go-chi/chi/v5"
	"github.com/proof-at-home/server/src/server/store"
)

type ConjectureHandler struct {
	Store store.Store
}

func (h *ConjectureHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	summaries := h.Store.ListConjectures()
	json.NewEncoder(w).Encode(summaries)
}

func (h *ConjectureHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := chi.URLParam(r, "id")
	p, ok := h.Store.GetConjecture(id)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(p)
}
