package gitstore

import (
	"fmt"
	"log/slog"
	"os/exec"
	"strings"
)

// LocalForge implements ForgeClient for local development.
// Instead of creating PRs on a remote forge, it merges branches directly
// into main and pushes to the local bare repo origin.
type LocalForge struct {
	repoPath string
}

func NewLocalForge(repoPath string) *LocalForge {
	return &LocalForge{repoPath: repoPath}
}

func (f *LocalForge) CreatePR(branch, base, title, body string) (string, error) {
	slog.Info("LocalForge: merging branch into base", "branch", branch, "base", base, "title", title)

	// Checkout base branch
	if err := f.git("checkout", base); err != nil {
		return "", fmt.Errorf("checking out %s: %w", base, err)
	}

	// Merge the branch with a merge commit
	if err := f.git("merge", branch, "--no-ff", "-m", title); err != nil {
		return "", fmt.Errorf("merging %s into %s: %w", branch, base, err)
	}

	// Push merged base to origin
	if err := f.git("push", "origin", base); err != nil {
		return "", fmt.Errorf("pushing %s: %w", base, err)
	}

	// Delete the merged branch
	if err := f.git("branch", "-d", branch); err != nil {
		slog.Warn("LocalForge: could not delete merged branch", "branch", branch, "error", err)
	}

	return fmt.Sprintf("local://merged/%s", branch), nil
}

func (f *LocalForge) VerifyWebhookSignature(payload []byte, signature string) bool {
	return true
}

func (f *LocalForge) RepoURL() string {
	return fmt.Sprintf("file://%s", f.repoPath)
}

func (f *LocalForge) git(args ...string) error {
	cmd := exec.Command("git", args...)
	cmd.Dir = f.repoPath
	out, err := cmd.CombinedOutput()
	if err != nil {
		return fmt.Errorf("%s: %s", strings.Join(args, " "), string(out))
	}
	return nil
}
