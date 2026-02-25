package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/go-chi/chi/v5"
	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
)

type CommandHandler struct {
	Store store.Store
}

func (h *CommandHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	commands := h.Store.ListCommands()
	if commands == nil {
		commands = []data.Command{}
	}
	json.NewEncoder(w).Encode(commands)
}

func (h *CommandHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	name := chi.URLParam(r, "name")
	cmd, ok := h.Store.GetCommand(name)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(cmd)
}
