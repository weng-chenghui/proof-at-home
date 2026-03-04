package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
	"github.com/proof-at-home/server/src/server/store/gitstore"
)

type VisualizationHandler struct {
	Store    store.Store
	GitStore *gitstore.GitStore
}

// List returns all visualizations. GET /visualizations
func (h *VisualizationHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	visualizations := h.Store.ListVisualizations()
	json.NewEncoder(w).Encode(visualizations)
}

// Get returns a single visualization by ID. GET /visualizations/{id}
func (h *VisualizationHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	v, ok := h.Store.GetVisualization(id)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(v)
}

// Submit creates a visualization via GitStore. POST /visualizations
func (h *VisualizationHandler) Submit(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var visualization data.Visualization
	if err := json.NewDecoder(r.Body).Decode(&visualization); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	commitSHA, err := h.GitStore.AddVisualization(visualization)
	if err != nil {
		http.Error(w, `{"error":"failed to create visualization: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "accepted",
	})
}

// SealVisualization commits NFT metadata and creates a PR. POST /visualizations/{id}/seal
func (h *VisualizationHandler) SealVisualization(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var nftMetadata any
	if err := json.NewDecoder(r.Body).Decode(&nftMetadata); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	prURL, err := h.GitStore.SealVisualization(id, nftMetadata)
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
