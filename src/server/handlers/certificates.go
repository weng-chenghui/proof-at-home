package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
)

type CertificateHandler struct {
	Store store.Store
}

func (h *CertificateHandler) Submit(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var result data.Certificate
	if err := json.NewDecoder(r.Body).Decode(&result); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	h.Store.AddCertificate(result)
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{"status": "accepted"})
}

func (h *CertificateHandler) SubmitBatch(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var summary data.ContributionSummary
	if err := json.NewDecoder(r.Body).Decode(&summary); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	h.Store.AddContribution(summary)
	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{"status": "accepted"})
}
