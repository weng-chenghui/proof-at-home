package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/go-chi/chi/v5"
	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
)

type StrategyHandler struct {
	Store store.Store
}

func (h *StrategyHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	commands := h.Store.ListStrategies()
	if commands == nil {
		commands = []data.Strategy{}
	}
	json.NewEncoder(w).Encode(commands)
}

func (h *StrategyHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	name := chi.URLParam(r, "name")
	cmd, ok := h.Store.GetStrategy(name)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(cmd)
}
