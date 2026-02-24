package handlers

import (
	"archive/tar"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"path/filepath"

	"github.com/go-chi/chi/v5"
	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store"
	"github.com/proof-at-home/server/src/server/store/gitstore"
)

type CertificateHandler struct {
	Store    store.Store
	GitStore *gitstore.GitStore
}

func (h *CertificateHandler) List(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	packages := h.Store.ListCertificatePackages()
	json.NewEncoder(w).Encode(packages)
}

func (h *CertificateHandler) ListCertificates(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	certificates := h.Store.ListCertificates()
	json.NewEncoder(w).Encode(certificates)
}

// DownloadArchive generates a tar.gz on-the-fly from the git clone's proofs directory.
// GET /certificate-packages/{contributionID}/archive
func (h *CertificateHandler) DownloadArchive(w http.ResponseWriter, r *http.Request) {
	contributionID := chi.URLParam(r, "contributionID")

	proofsDir := filepath.Join(h.GitStore.RepoPath(), "contributions", contributionID, "proofs")
	if _, err := os.Stat(proofsDir); os.IsNotExist(err) {
		w.Header().Set("Content-Type", "application/json")
		http.Error(w, `{"error":"archive not found"}`, http.StatusNotFound)
		return
	}

	w.Header().Set("Content-Type", "application/gzip")
	w.Header().Set("Content-Disposition", fmt.Sprintf("attachment; filename=%s-proofs.tar.gz", contributionID))

	gw := gzip.NewWriter(w)
	defer gw.Close()
	tw := tar.NewWriter(gw)
	defer tw.Close()

	entries, err := os.ReadDir(proofsDir)
	if err != nil {
		slog.Error("Failed to read proofs dir", "error", err, "path", proofsDir)
		return
	}

	for _, entry := range entries {
		if entry.IsDir() {
			continue
		}
		filePath := filepath.Join(proofsDir, entry.Name())
		info, err := entry.Info()
		if err != nil {
			continue
		}
		header, err := tar.FileInfoHeader(info, "")
		if err != nil {
			continue
		}
		header.Name = entry.Name()
		if err := tw.WriteHeader(header); err != nil {
			slog.Error("Failed to write tar header", "error", err)
			return
		}
		f, err := os.Open(filePath)
		if err != nil {
			continue
		}
		io.Copy(tw, f)
		f.Close()
	}
}

// SubmitCertificate creates a certificate via GitStore. POST /certificates
func (h *CertificateHandler) SubmitCertificate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	var certificate data.CertificateSummary
	if err := json.NewDecoder(r.Body).Decode(&certificate); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	commitSHA, err := h.GitStore.AddCertificate(certificate)
	if err != nil {
		http.Error(w, `{"error":"failed to create certificate: `+err.Error()+`"}`, http.StatusInternalServerError)
		return
	}

	w.WriteHeader(http.StatusCreated)
	json.NewEncoder(w).Encode(map[string]string{
		"commit_sha": commitSHA,
		"status":     "accepted",
	})
}

// SealCertificate commits NFT metadata and creates a PR. POST /certificates/{id}/seal
func (h *CertificateHandler) SealCertificate(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	id := r.PathValue("id")

	var nftMetadata any
	if err := json.NewDecoder(r.Body).Decode(&nftMetadata); err != nil {
		http.Error(w, `{"error":"invalid JSON"}`, http.StatusBadRequest)
		return
	}

	prURL, err := h.GitStore.SealCertificate(id, nftMetadata)
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
