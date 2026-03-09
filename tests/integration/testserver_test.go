package integration

import (
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"

	"github.com/proof-at-home/server/src/server/app"
	"github.com/proof-at-home/server/src/server/config"
)

// serverURL is set by TestMain and used by all test helpers.
var serverURL string

func TestMain(m *testing.M) {
	// Priority 1: explicit TEST_SERVER_URL (PocketBase CI, etc.)
	if u := os.Getenv("TEST_SERVER_URL"); u != "" {
		serverURL = u
		if err := waitForHealth(serverURL); err != nil {
			fmt.Fprintf(os.Stderr, "FATAL: server at %s not healthy: %v\n", serverURL, err)
			os.Exit(1)
		}
		os.Exit(m.Run())
	}

	// Priority 2: localhost:8080 already running
	if err := waitForHealth("http://localhost:8080"); err == nil {
		serverURL = "http://localhost:8080"
		os.Exit(m.Run())
	}

	// Priority 3: spin up in-process server
	tmpDir, err := os.MkdirTemp("", "pah-integ-*")
	if err != nil {
		fmt.Fprintf(os.Stderr, "FATAL: create tmpdir: %v\n", err)
		os.Exit(1)
	}
	defer os.RemoveAll(tmpDir)

	projectRoot, err := findProjectRoot()
	if err != nil {
		fmt.Fprintf(os.Stderr, "FATAL: find project root: %v\n", err)
		os.Exit(1)
	}

	bareRepo := filepath.Join(tmpDir, "data-repo.git")
	if err := setupDevRepo(tmpDir, bareRepo, projectRoot); err != nil {
		fmt.Fprintf(os.Stderr, "FATAL: setup dev repo: %v\n", err)
		os.Exit(1)
	}

	dbPath := filepath.Join(tmpDir, "test.db")

	cfg := &config.Config{
		Port:            "0", // unused by httptest
		DatabasePath:    dbPath,
		GitDataRepoURL:  bareRepo,
		GitDataRepoPath: filepath.Join(tmpDir, "data"),
		GitForgeType:    "local",
		CORSOrigins:     []string{"*"},
		LogLevel:        "warn",
	}

	a, err := app.New(cfg)
	if err != nil {
		fmt.Fprintf(os.Stderr, "FATAL: app.New: %v\n", err)
		os.Exit(1)
	}
	defer a.Close()

	ts := httptest.NewServer(a.Handler)
	defer ts.Close()
	serverURL = ts.URL

	os.Exit(m.Run())
}

// waitForHealth checks if the server is reachable and healthy.
func waitForHealth(base string) error {
	client := &http.Client{Timeout: 2 * time.Second}
	resp, err := client.Get(base + "/health")
	if err != nil {
		return err
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("health returned %d", resp.StatusCode)
	}
	return nil
}

// findProjectRoot walks up from cwd looking for go.mod.
func findProjectRoot() (string, error) {
	dir, err := os.Getwd()
	if err != nil {
		return "", err
	}
	for {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			return dir, nil
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return "", fmt.Errorf("go.mod not found in any parent directory")
		}
		dir = parent
	}
}

// setupDevRepo replicates scripts/dev-setup.sh in Go:
// creates a bare repo, clones it, copies example data, commits, and pushes.
func setupDevRepo(tmpDir, bareRepo, projectRoot string) error {
	exampleData := filepath.Join(projectRoot, "examples", "data-repo")
	if _, err := os.Stat(exampleData); err != nil {
		return fmt.Errorf("example data not found at %s: %w", exampleData, err)
	}

	// 1. Create bare repo
	if out, err := exec.Command("git", "init", "--bare", "--initial-branch=main", bareRepo).CombinedOutput(); err != nil {
		return fmt.Errorf("git init bare: %s: %w", out, err)
	}

	// 2. Clone into temp working copy
	workDir := filepath.Join(tmpDir, "work")
	if out, err := exec.Command("git", "clone", bareRepo, workDir).CombinedOutput(); err != nil {
		return fmt.Errorf("git clone: %s: %w", out, err)
	}

	// 3. Copy example data
	// Use cp -r to copy all contents
	entries, err := os.ReadDir(exampleData)
	if err != nil {
		return fmt.Errorf("reading example data: %w", err)
	}
	for _, e := range entries {
		src := filepath.Join(exampleData, e.Name())
		dst := filepath.Join(workDir, e.Name())
		if out, err := exec.Command("cp", "-r", src, dst).CombinedOutput(); err != nil {
			return fmt.Errorf("cp %s: %s: %w", e.Name(), out, err)
		}
	}

	// 4. Configure git identity on the temp repo (not global)
	cmds := [][]string{
		{"git", "-C", workDir, "config", "user.email", "test@proof-at-home.local"},
		{"git", "-C", workDir, "config", "user.name", "Proof@Home Test"},
		{"git", "-C", workDir, "add", "-A"},
		{"git", "-C", workDir, "commit", "-m", "Initial test data"},
		{"git", "-C", workDir, "push", "origin", "main"},
	}
	for _, args := range cmds {
		if out, err := exec.Command(args[0], args[1:]...).CombinedOutput(); err != nil {
			return fmt.Errorf("%s: %s: %w", args[1], out, err)
		}
	}

	return nil
}
