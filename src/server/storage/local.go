package storage

import (
	"context"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"time"
)

// LocalStorage stores files on the local filesystem.
type LocalStorage struct {
	baseDir string
	baseURL string
}

// NewLocal creates a local filesystem storage.
// baseDir is the directory where files are stored.
// baseURL is the URL prefix for generating download URLs (e.g., "/files").
func NewLocal(baseDir, baseURL string) (*LocalStorage, error) {
	if err := os.MkdirAll(baseDir, 0o755); err != nil {
		return nil, fmt.Errorf("creating storage dir: %w", err)
	}
	return &LocalStorage{
		baseDir: baseDir,
		baseURL: baseURL,
	}, nil
}

func (s *LocalStorage) Upload(_ context.Context, key string, reader io.Reader, _ string) error {
	path := filepath.Join(s.baseDir, key)
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}

	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()

	_, err = io.Copy(f, reader)
	return err
}

func (s *LocalStorage) PresignedURL(_ context.Context, key string, _ time.Duration) (string, error) {
	return fmt.Sprintf("%s/%s", s.baseURL, key), nil
}

func (s *LocalStorage) Ping(_ context.Context) error {
	_, err := os.Stat(s.baseDir)
	return err
}
