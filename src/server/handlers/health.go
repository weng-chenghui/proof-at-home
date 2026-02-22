package handlers

import (
	"context"
	"encoding/json"
	"net/http"
	"time"

	"github.com/proof-at-home/server/src/server/storage"
)

// Pinger is implemented by stores that support health checks (e.g., PostgresStore).
type Pinger interface {
	Ping(ctx context.Context) error
}

type HealthHandler struct {
	Store   interface{} // may implement Pinger
	Storage storage.ObjectStorage
}

type healthResponse struct {
	Status string            `json:"status"`
	Checks map[string]string `json:"checks"`
}

func (h *HealthHandler) Check(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	ctx, cancel := context.WithTimeout(r.Context(), 3*time.Second)
	defer cancel()

	checks := make(map[string]string)
	allOK := true

	// Check database if store supports Ping
	if pinger, ok := h.Store.(Pinger); ok {
		if err := pinger.Ping(ctx); err != nil {
			checks["database"] = "error: " + err.Error()
			allOK = false
		} else {
			checks["database"] = "ok"
		}
	}

	// Check object storage
	if h.Storage != nil {
		if err := h.Storage.Ping(ctx); err != nil {
			checks["storage"] = "error: " + err.Error()
			allOK = false
		} else {
			checks["storage"] = "ok"
		}
	}

	resp := healthResponse{
		Status: "ok",
		Checks: checks,
	}

	if !allOK {
		resp.Status = "degraded"
		w.WriteHeader(http.StatusServiceUnavailable)
	}

	json.NewEncoder(w).Encode(resp)
}
