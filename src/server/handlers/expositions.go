package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
	"github.com/proof-at-home/server/src/server/store/gitstore"
)

type ExpositionHandler struct {
	Store    store.Store
	GitStore *gitstore.GitStore
}

// List returns all expositions. GET /expositions
func (h *ExpositionHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	expositions := h.Store.ListExpositions()
	json.NewEncoder(w).Encode(expositions)
}

// Get returns a single exposition by ID. GET /expositions/{id}
func (h *ExpositionHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	e, ok := h.Store.GetExposition(id)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(e)
}

// Submit creates an exposition via GitStore. POST /expositions
func (h *ExpositionHandler) Submit(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var exposition data.Exposition
	if err := json.NewDecoder(r.Body).Decode(&exposition); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	commitSHA, err := h.GitStore.AddExposition(exposition)
	if err != nil {
		http.Error(w, `{"error":"failed to create exposition: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "accepted",
	})
}

// SealExposition commits NFT metadata and creates a PR. POST /expositions/{id}/seal
func (h *ExpositionHandler) SealExposition(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var nftMetadata any
	if err := json.NewDecoder(r.Body).Decode(&nftMetadata); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	prURL, err := h.GitStore.SealExposition(id, nftMetadata)
	if err != nil {
		http.Error(w, `{"error":"failed to seal: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{
		"pr_url": prURL,
		"status": "pending",
	})
}
