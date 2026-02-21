package handlers

import (
	"encoding/json"
	"net/http"
	"strings"

	"github.com/proof-at-home/server/src/server/store"
)

type ProblemHandler struct {
	Store *store.MemoryStore
}

func (h *ProblemHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	path := strings.TrimPrefix(r.URL.Path, "/problems")
	path = strings.TrimPrefix(path, "/")

	if path == "" {
		h.listProblems(w, r)
	} else {
		h.getProblem(w, r, path)
	}
}

func (h *ProblemHandler) listProblems(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		http.Error(w, `{"error":"method not allowed"}`, http.StatusMethodNotAllowed)
		return
	}
	summaries := h.Store.ListProblems()
	json.NewEncoder(w).Encode(summaries)
}

func (h *ProblemHandler) getProblem(w http.ResponseWriter, r *http.Request, id string) {
	if r.Method != http.MethodGet {
		http.Error(w, `{"error":"method not allowed"}`, http.StatusMethodNotAllowed)
		return
	}
	p, ok := h.Store.GetProblem(id)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(p)
}
