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
// Also accepts visualization-format payloads (with viz_json field) for backward compatibility.
func (h *ExpositionHandler) Submit(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	// Decode into a generic map first to detect viz-format submissions
	var raw map[string]json.RawMessage
	if err := json.NewDecoder(r.Body).Decode(&raw); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	// Re-encode and decode into Exposition struct
	rawBytes, _ := json.Marshal(raw)
	var exposition data.Exposition
	if err := json.Unmarshal(rawBytes, &exposition); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	// Handle visualization-format: use visualization_id as exposition_id, viz_json as exposition_text
	if _, hasVizJSON := raw["viz_json"]; hasVizJSON {
		if exposition.ExpositionID == "" {
			if vizIDRaw, ok := raw["visualization_id"]; ok {
				var vizID string
				json.Unmarshal(vizIDRaw, &vizID)
				exposition.ExpositionID = vizID
			}
		}
		if exposition.ExpositionText == "" {
			exposition.ExpositionText = string(raw["viz_json"])
		}
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
