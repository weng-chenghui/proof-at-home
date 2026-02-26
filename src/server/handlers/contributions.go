package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
	"github.com/proof-at-home/server/src/server/store/gitstore"
)

type ContributionHandler struct {
	Store    store.Store
	GitStore *gitstore.GitStore
}

// List returns all contributions. GET /contributions
func (h *ContributionHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	contributions := h.Store.ListContributions()
	json.NewEncoder(w).Encode(contributions)
}

// Get returns a single contribution. GET /contributions/{id}
func (h *ContributionHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")
	cs, ok := h.Store.GetContribution(id)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(cs)
}

// Create registers a new contribution. POST /contributions
// Writes to GitStore (creates branch, commits summary.json).
func (h *ContributionHandler) Create(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var summary data.Contribution
	if err := json.NewDecoder(r.Body).Decode(&summary); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	if err := h.GitStore.AddContribution(summary); err != nil {
		http.Error(w, `{"error":"failed to create contribution: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{"status": "accepted"})
}

// Update finalizes a contribution (cost totals, proof_status).
// PATCH /contributions/{id}
// Returns the git commit SHA for the client to sign.
func (h *ContributionHandler) Update(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var summary data.Contribution
	if err := json.NewDecoder(r.Body).Decode(&summary); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	summary.ContributionID = id
	commitSHA, err := h.GitStore.FinalizeContribution(id, summary)
	if err != nil {
		http.Error(w, `{"error":"failed to finalize: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "pending",
	})
}

// SubmitProof adds a proof result to a contribution. POST /contributions/{id}/proofs
func (h *ContributionHandler) SubmitProof(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var result data.Proof
	if err := json.NewDecoder(r.Body).Decode(&result); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	result.ContributionID = id
	if err := h.GitStore.AddProof(result); err != nil {
		http.Error(w, `{"error":"failed to add result: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{"status": "accepted"})
}

// ListProofs returns results for a contribution. GET /contributions/{id}/proofs
func (h *ContributionHandler) ListProofs(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")
	results := h.Store.ListProofs(id)
	if results == nil {
		results = []data.Proof{}
	}
	json.NewEncoder(w).Encode(results)
}

// Seal commits NFT metadata and creates a PR. POST /contributions/{id}/seal
func (h *ContributionHandler) Seal(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var nftMetadata any
	if err := json.NewDecoder(r.Body).Decode(&nftMetadata); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	prURL, err := h.GitStore.SealContribution(id, nftMetadata)
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
