package handlers

import (
	"archive/tar"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/google/uuid"
	"github.com/proof-at-home/server/src/server/data"
	"github.com/proof-at-home/server/src/server/store/gitstore"
)

type PackageHandler struct {
	GitStore *gitstore.GitStore
}

type packageSubmitResponse struct {
	Status             string   `json:"status"`
	AddedConjectureIDs []string `json:"added_conjecture_ids"`
	Count              int      `json:"count"`
}

func (h *PackageHandler) Submit(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")

	ct := r.Header.Get("Content-Type")

	var added []string
	var err error

	switch {
	case strings.HasPrefix(ct, "application/gzip"):
		added, err = h.handleTarGz(r)
	case strings.HasPrefix(ct, "application/json"):
		added, err = h.handleGitURL(r)
	default:
		http.Error(w, `{"error":"unsupported content type"}`, http.StatusBadRequest)
		return
	}

	if err != nil {
		http.Error(w, fmt.Sprintf(`{"error":%q}`, err.Error()), http.StatusBadRequest)
		return
	}

	resp := packageSubmitResponse{
		Status:             "accepted",
		AddedConjectureIDs: added,
		Count:              len(added),
	}
	if resp.AddedConjectureIDs == nil {
		resp.AddedConjectureIDs = []string{}
	}
	json.NewEncoder(w).Encode(resp)
}

func (h *PackageHandler) handleTarGz(r *http.Request) ([]string, error) {
	tmpDir, err := os.MkdirTemp("", "pkg-tar-*")
	if err != nil {
		return nil, fmt.Errorf("creating temp dir: %w", err)
	}
	defer os.RemoveAll(tmpDir)

	if err := extractTarGz(r.Body, tmpDir); err != nil {
		return nil, fmt.Errorf("extracting tar.gz: %w", err)
	}

	conjectures, err := loadConjecturesFromDir(tmpDir)
	if err != nil {
		return nil, err
	}

	batchID := uuid.New().String()
	prURL, err := h.GitStore.AddConjectures(conjectures, batchID)
	if err != nil {
		return nil, fmt.Errorf("adding conjectures via git: %w", err)
	}
	_ = prURL // PR URL created but IDs derived from conjectures
	ids := make([]string, len(conjectures))
	for i, c := range conjectures {
		ids[i] = c.ID
	}
	return ids, nil
}

func (h *PackageHandler) handleGitURL(r *http.Request) ([]string, error) {
	var body struct {
		GitURL string `json:"git_url"`
	}
	if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
		return nil, fmt.Errorf("invalid JSON body: %w", err)
	}
	if body.GitURL == "" {
		return nil, fmt.Errorf("git_url is required")
	}

	tmpDir, err := os.MkdirTemp("", "pkg-git-*")
	if err != nil {
		return nil, fmt.Errorf("creating temp dir: %w", err)
	}
	defer os.RemoveAll(tmpDir)

	cmd := exec.Command("git", "clone", "--depth", "1", body.GitURL, tmpDir)
	if out, err := cmd.CombinedOutput(); err != nil {
		return nil, fmt.Errorf("git clone failed: %s: %w", string(out), err)
	}

	conjectures, err := loadConjecturesFromDir(tmpDir)
	if err != nil {
		return nil, err
	}

	batchID := uuid.New().String()
	prURL, err := h.GitStore.AddConjectures(conjectures, batchID)
	if err != nil {
		return nil, fmt.Errorf("adding conjectures via git: %w", err)
	}
	_ = prURL
	ids := make([]string, len(conjectures))
	for i, c := range conjectures {
		ids[i] = c.ID
	}
	return ids, nil
}

func extractTarGz(r io.Reader, destDir string) error {
	gz, err := gzip.NewReader(r)
	if err != nil {
		return err
	}
	defer gz.Close()

	tr := tar.NewReader(gz)
	for {
		hdr, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}

		// Reject path traversal
		clean := filepath.Clean(hdr.Name)
		if strings.HasPrefix(clean, "..") || strings.Contains(clean, string(filepath.Separator)+"..") {
			continue
		}

		target := filepath.Join(destDir, clean)
		if !strings.HasPrefix(target, destDir) {
			continue
		}

		switch hdr.Typeflag {
		case tar.TypeDir:
			os.MkdirAll(target, 0o755)
		case tar.TypeReg:
			os.MkdirAll(filepath.Dir(target), 0o755)
			f, err := os.Create(target)
			if err != nil {
				return err
			}
			if _, err := io.Copy(f, tr); err != nil {
				f.Close()
				return err
			}
			f.Close()
		}
	}
	return nil
}

func loadConjecturesFromDir(dir string) ([]data.Conjecture, error) {
	var conjectures []data.Conjecture
	err := filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return nil // skip errors
		}
		if info.IsDir() || filepath.Ext(path) != ".json" {
			return nil
		}
		raw, err := os.ReadFile(path)
		if err != nil {
			return nil
		}
		var c data.Conjecture
		if err := json.Unmarshal(raw, &c); err != nil {
			return nil // skip invalid files
		}
		if c.ID == "" {
			return nil // skip conjectures without ID
		}
		conjectures = append(conjectures, c)
		return nil
	})
	if err != nil {
		return nil, fmt.Errorf("walking directory: %w", err)
	}
	return conjectures, nil
}
