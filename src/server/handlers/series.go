package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
	"github.com/proof-at-home/server/src/server/store/gitstore"
)

type SeriesHandler struct {
	Store    store.Store
	GitStore *gitstore.GitStore
}

// List returns all series, with optional difficulty filter. GET /series
func (h *SeriesHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	series := h.Store.ListSeries()
	if series == nil {
		series = []data.Series{}
	}

	difficulty := r.URL.Query().Get("difficulty")
	if difficulty != "" {
		var filtered []data.Series
		for _, s := range series {
			if s.Difficulty != difficulty {
				continue
			}
			filtered = append(filtered, s)
		}
		if filtered == nil {
			filtered = []data.Series{}
		}
		json.NewEncoder(w).Encode(filtered)
		return
	}

	json.NewEncoder(w).Encode(series)
}

// Get returns a single series by ID. GET /series/{id}
func (h *SeriesHandler) Get(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	s, ok := h.Store.GetSeries(id)
	if !ok {
		http.Error(w, `{"error":"not found"}`, http.StatusNotFound)
		return
	}
	json.NewEncoder(w).Encode(s)
}

// Create creates a series via GitStore. POST /series
func (h *SeriesHandler) Create(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var series data.Series
	if err := json.NewDecoder(r.Body).Decode(&series); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	if series.SeriesID == "" || series.Title == "" || series.AuthorUsername == "" {
		http.Error(w, `{"error":"series_id, title, and author_username are required"}`, http.StatusBadRequest)
		return
	}

	commitSHA, err := h.GitStore.AddSeries(series)
	if err != nil {
		http.Error(w, `{"error":"failed to create series: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "accepted",
	})
}

// Update updates a series via GitStore. PATCH /series/{id}
func (h *SeriesHandler) Update(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var series data.Series
	if err := json.NewDecoder(r.Body).Decode(&series); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	series.SeriesID = id

	commitSHA, err := h.GitStore.UpdateSeries(id, series)
	if err != nil {
		http.Error(w, `{"error":"failed to update series: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "accepted",
	})
}
