package gitstore

import (
	"encoding/json"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"

	"github.com/proof-at-home/server/src/server/data"
)

// GitStore manages a local clone of the data git repo.
// All write operations create branches, commit files, and push.
// Read operations are served from the SQLite cache (not this struct).
type GitStore struct {
	mu       sync.Mutex
	repoPath string
	repoURL  string
	forge    ForgeClient
}

// New creates a GitStore. It clones the repo if not already present,
// or pulls latest main if the clone already exists.
func New(repoURL, repoPath string, forge ForgeClient) (*GitStore, error) {
	gs := &GitStore{
		repoPath: repoPath,
		repoURL:  repoURL,
		forge:    forge,
	}

	if _, err := os.Stat(filepath.Join(repoPath, ".git")); os.IsNotExist(err) {
		slog.Info("Cloning data repo", "url", repoURL, "path", repoPath)
		if err := gs.git("clone", repoURL, repoPath); err != nil {
			return nil, fmt.Errorf("cloning data repo: %w", err)
		}
	} else {
		slog.Info("Data repo already cloned, pulling latest", "path", repoPath)
		if err := gs.gitInRepo("checkout", "main"); err != nil {
			return nil, fmt.Errorf("checking out main: %w", err)
		}
		if err := gs.gitInRepo("pull", "origin", "main"); err != nil {
			return nil, fmt.Errorf("pulling latest: %w", err)
		}
	}

	return gs, nil
}

// RepoPath returns the local filesystem path of the git clone.
func (gs *GitStore) RepoPath() string {
	return gs.repoPath
}

// Forge returns the forge client for webhook verification etc.
func (gs *GitStore) Forge() ForgeClient {
	return gs.forge
}

// ── Contribution operations ──

// AddContribution creates a branch and commits the initial summary.json.
func (gs *GitStore) AddContribution(cs data.ContributionSummary) error {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("contrib/%s", cs.ContributionID)
	dir := filepath.Join("contributions", cs.ContributionID)

	if err := gs.createBranch(branch); err != nil {
		return err
	}

	if err := gs.writeJSON(filepath.Join(dir, "summary.json"), cs); err != nil {
		return err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Add contribution %s", cs.ContributionID)); err != nil {
		return err
	}

	return nil
}

// AddContributionResult commits a result and proof file to the contribution branch.
func (gs *GitStore) AddContributionResult(r data.ContributionResult) error {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("contrib/%s", r.ContributionID)

	if err := gs.checkoutBranch(branch); err != nil {
		return err
	}

	dir := filepath.Join("contributions", r.ContributionID)

	// Write result JSON
	resultPath := filepath.Join(dir, "results", r.ConjectureID+".json")
	if err := gs.writeJSON(resultPath, r); err != nil {
		return err
	}

	// Write proof script file
	if r.ProofScript != "" {
		ext := ".v" // default to Rocq
		proofPath := filepath.Join(dir, "proofs", r.ConjectureID+ext)
		absPath := filepath.Join(gs.repoPath, proofPath)
		if err := os.MkdirAll(filepath.Dir(absPath), 0o755); err != nil {
			return fmt.Errorf("creating proofs dir: %w", err)
		}
		if err := os.WriteFile(absPath, []byte(r.ProofScript), 0o644); err != nil {
			return fmt.Errorf("writing proof file: %w", err)
		}
	}

	msg := fmt.Sprintf("Add result for %s in contribution %s", r.ConjectureID, r.ContributionID)
	if err := gs.commitAndPush(branch, msg); err != nil {
		return err
	}

	return nil
}

// FinalizeContribution updates summary.json with cost/status and returns the commit SHA.
func (gs *GitStore) FinalizeContribution(id string, cs data.ContributionSummary) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("contrib/%s", id)

	if err := gs.checkoutBranch(branch); err != nil {
		return "", err
	}

	dir := filepath.Join("contributions", id)
	if err := gs.writeJSON(filepath.Join(dir, "summary.json"), cs); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Finalize contribution %s", id)); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	return sha, nil
}

// SealContribution writes nft_metadata.json, commits, pushes, and creates a PR.
func (gs *GitStore) SealContribution(id string, nftMetadata any) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("contrib/%s", id)

	if err := gs.checkoutBranch(branch); err != nil {
		return "", err
	}

	dir := filepath.Join("contributions", id)
	if err := gs.writeJSON(filepath.Join(dir, "nft_metadata.json"), nftMetadata); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Seal contribution %s with NFT metadata", id)); err != nil {
		return "", err
	}

	prURL, err := gs.forge.CreatePR(
		branch, "main",
		fmt.Sprintf("Contribution: %s", id),
		fmt.Sprintf("Sealed contribution `%s` with NFT metadata.", id),
	)
	if err != nil {
		return "", fmt.Errorf("creating PR: %w", err)
	}

	return prURL, nil
}

// ── Certificate operations ──

// AddCertificate creates a branch and commits the certificate summary.
func (gs *GitStore) AddCertificate(cs data.CertificateSummary) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("cert/%s", cs.CertificateID)
	dir := filepath.Join("certificates", cs.CertificateID)

	if err := gs.createBranch(branch); err != nil {
		return "", err
	}

	if err := gs.writeJSON(filepath.Join(dir, "summary.json"), cs); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Add certificate %s", cs.CertificateID)); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	return sha, nil
}

// SealCertificate writes nft_metadata.json, commits, pushes, and creates a PR.
func (gs *GitStore) SealCertificate(id string, nftMetadata any) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("cert/%s", id)

	if err := gs.checkoutBranch(branch); err != nil {
		return "", err
	}

	dir := filepath.Join("certificates", id)
	if err := gs.writeJSON(filepath.Join(dir, "nft_metadata.json"), nftMetadata); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Seal certificate %s with NFT metadata", id)); err != nil {
		return "", err
	}

	prURL, err := gs.forge.CreatePR(
		branch, "main",
		fmt.Sprintf("Certificate: %s", id),
		fmt.Sprintf("Sealed certificate `%s` with NFT metadata.", id),
	)
	if err != nil {
		return "", fmt.Errorf("creating PR: %w", err)
	}

	return prURL, nil
}

// ── Conjecture operations ──

// AddConjectures creates a branch, writes conjecture JSON files, commits, and creates a PR.
func (gs *GitStore) AddConjectures(conjectures []data.Conjecture, batchID string) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("conj/%s", batchID)

	if err := gs.createBranch(branch); err != nil {
		return "", err
	}

	for _, c := range conjectures {
		path := filepath.Join("conjectures", c.ID+".json")
		if err := gs.writeJSON(path, c); err != nil {
			return "", err
		}
	}

	msg := fmt.Sprintf("Add %d conjectures (batch %s)", len(conjectures), batchID)
	if err := gs.commitAndPush(branch, msg); err != nil {
		return "", err
	}

	prURL, err := gs.forge.CreatePR(
		branch, "main",
		fmt.Sprintf("Conjectures: batch %s (%d)", batchID, len(conjectures)),
		msg,
	)
	if err != nil {
		return "", fmt.Errorf("creating PR: %w", err)
	}

	return prURL, nil
}

// ── Cache rebuild ──

// PullAndRebuild pulls latest main and calls the rebuild function.
// The rebuild func is provided by the caller (typically SQLiteStore.RebuildFromDir).
func (gs *GitStore) PullAndRebuild(rebuildFn func(repoPath string) error) error {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	if err := gs.gitInRepo("checkout", "main"); err != nil {
		return fmt.Errorf("checking out main: %w", err)
	}
	if err := gs.gitInRepo("pull", "origin", "main"); err != nil {
		return fmt.Errorf("pulling latest: %w", err)
	}

	return rebuildFn(gs.repoPath)
}

// ── Internal git helpers ──

func (gs *GitStore) git(args ...string) error {
	cmd := exec.Command("git", args...)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	slog.Debug("git", "args", strings.Join(args, " "))
	return cmd.Run()
}

func (gs *GitStore) gitInRepo(args ...string) error {
	cmd := exec.Command("git", args...)
	cmd.Dir = gs.repoPath
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	slog.Debug("git", "dir", gs.repoPath, "args", strings.Join(args, " "))
	return cmd.Run()
}

func (gs *GitStore) gitOutput(args ...string) (string, error) {
	cmd := exec.Command("git", args...)
	cmd.Dir = gs.repoPath
	out, err := cmd.Output()
	if err != nil {
		return "", fmt.Errorf("git %s: %w", strings.Join(args, " "), err)
	}
	return strings.TrimSpace(string(out)), nil
}

func (gs *GitStore) createBranch(branch string) error {
	// Start from latest main
	if err := gs.gitInRepo("checkout", "main"); err != nil {
		return fmt.Errorf("checking out main: %w", err)
	}
	if err := gs.gitInRepo("pull", "origin", "main"); err != nil {
		slog.Warn("Could not pull latest main", "error", err)
	}
	if err := gs.gitInRepo("checkout", "-b", branch); err != nil {
		return fmt.Errorf("creating branch %s: %w", branch, err)
	}
	return nil
}

func (gs *GitStore) checkoutBranch(branch string) error {
	if err := gs.gitInRepo("checkout", branch); err != nil {
		return fmt.Errorf("checking out branch %s: %w", branch, err)
	}
	return nil
}

func (gs *GitStore) writeJSON(relPath string, v any) error {
	absPath := filepath.Join(gs.repoPath, relPath)
	if err := os.MkdirAll(filepath.Dir(absPath), 0o755); err != nil {
		return fmt.Errorf("creating directory for %s: %w", relPath, err)
	}

	data, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return fmt.Errorf("marshaling JSON for %s: %w", relPath, err)
	}

	if err := os.WriteFile(absPath, data, 0o644); err != nil {
		return fmt.Errorf("writing %s: %w", relPath, err)
	}

	return nil
}

func (gs *GitStore) commitAndPush(branch, message string) error {
	if err := gs.gitInRepo("add", "-A"); err != nil {
		return fmt.Errorf("staging files: %w", err)
	}
	if err := gs.gitInRepo("commit", "-m", message); err != nil {
		return fmt.Errorf("committing: %w", err)
	}
	if err := gs.gitInRepo("push", "-u", "origin", branch); err != nil {
		return fmt.Errorf("pushing branch %s: %w", branch, err)
	}
	return nil
}

func (gs *GitStore) getHeadSHA() (string, error) {
	return gs.gitOutput("rev-parse", "HEAD")
}
