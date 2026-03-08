package handlers

import (
	"encoding/json"
	"fmt"
	"net/http"

	"github.com/go-chi/chi/v5"
	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
	"github.com/proof-at-home/server/src/server/store/gitstore"
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

	// Filter by kind query param
	if kind := r.URL.Query().Get("kind"); kind != "" {
		filtered := make([]data.Strategy, 0)
		for _, s := range commands {
			if s.Kind == kind {
				filtered = append(filtered, s)
			}
		}
		commands = filtered
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

type StrategyWriteHandler struct {
	GitStore *gitstore.GitStore
}

// Submit handles POST /strategies — write a strategy/memory to git.
func (h *StrategyWriteHandler) Submit(w http.ResponseWriter, r *http.Request) {
	var req struct {
		Name    string `json:"name"`
		Content string `json:"content"`
	}
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}
	if req.Name == "" || req.Content == "" {
		http.Error(w, `{"error":"name and content are required"}`, http.StatusBadRequest)
		return
	}

	sha, err := h.GitStore.AddStrategy(req.Name, []byte(req.Content))
	if err != nil {
		http.Error(w, fmt.Sprintf(`{"error":%q}`, err.Error()), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]string{
		"status":     "created",
		"commit_sha": sha,
	})
}

// SealStrategy handles POST /strategies/{name}/seal — seal a strategy with NFT metadata.
func (h *StrategyWriteHandler) SealStrategy(w http.ResponseWriter, r *http.Request) {
	name := chi.URLParam(r, "name")
	if name == "" {
		http.Error(w, `{"error":"name is required"}`, http.StatusBadRequest)
		return
	}

	var nftMetadata any
	if err := json.NewDecoder(r.Body).Decode(&nftMetadata); err != nil {
		http.Error(w, `{"error":"invalid JSON body"}`, http.StatusBadRequest)
		return
	}

	prURL, err := h.GitStore.SealStrategy(name, nftMetadata)
	if err != nil {
		http.Error(w, fmt.Sprintf(`{"error":%q}`, err.Error()), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]string{
		"status": "sealed",
		"pr_url": prURL,
	})
}
