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
	"time"

	toml "github.com/pelletier/go-toml/v2"
	"github.com/proof-at-home/server/src/server/data"
)

// ── Credits helpers ──

// initialCredits builds a CREDITS.toml for a newly created lesson or series.
func initialCredits(authorUsername, commitSHA string) *data.Credits {
	today := time.Now().UTC().Format("2006-01-02")
	return &data.Credits{
		Contributors: []data.CreditEntry{
			{
				Username:    authorUsername,
				Role:        "author",
				FirstCommit: commitSHA,
			},
		},
		Edition: data.EditionInfo{
			Current: 1,
			History: []data.EditionRecord{
				{Edition: 1, Date: today, Commit: commitSHA, Summary: "Initial release"},
			},
		},
		License: data.LicenseInfo{SPDX: "CC0-1.0"},
	}
}

// ensureContributor adds username as a contributor if not already present.
func ensureContributor(credits *data.Credits, username, commitSHA string) {
	for _, c := range credits.Contributors {
		if c.Username == username {
			return
		}
	}
	credits.Contributors = append(credits.Contributors, data.CreditEntry{
		Username:    username,
		Role:        "contributor",
		FirstCommit: commitSHA,
	})
}

// writeCredits writes a CREDITS.toml file into the repo.
func (gs *GitStore) writeCredits(relPath string, credits *data.Credits) error {
	absPath := filepath.Join(gs.repoPath, relPath)
	if err := os.MkdirAll(filepath.Dir(absPath), 0o755); err != nil {
		return fmt.Errorf("creating directory for %s: %w", relPath, err)
	}
	raw, err := data.RenderCreditsFile(credits)
	if err != nil {
		return fmt.Errorf("rendering credits: %w", err)
	}
	return os.WriteFile(absPath, raw, 0o644)
}

// readCredits reads and parses CREDITS.toml from the repo, returning nil if not found.
func (gs *GitStore) readCredits(relPath string) *data.Credits {
	absPath := filepath.Join(gs.repoPath, relPath)
	raw, err := os.ReadFile(absPath)
	if err != nil {
		return nil
	}
	credits, err := data.ParseCreditsFile(raw)
	if err != nil {
		slog.Warn("readCredits: failed to parse", "path", relPath, "error", err)
		return nil
	}
	return credits
}

// GitStore manages a local clone of the data git repo.
// All write operations create branches, commit files, and push.
// Read operations are served from the SQLite cache (not this struct).
type GitStore struct {
	mu            sync.Mutex
	repoPath      string
	repoURL       string
	forge         ForgeClient
	rebuildFn     func(repoPath string) error
	postRebuildFn func()
}

// SetRebuildFn sets the callback invoked after each merge to rebuild the read cache.
func (gs *GitStore) SetRebuildFn(fn func(repoPath string) error) {
	gs.rebuildFn = fn
}

// SetPostRebuildFn sets a callback invoked after each rebuild completes.
func (gs *GitStore) SetPostRebuildFn(fn func()) {
	gs.postRebuildFn = fn
}

// triggerRebuild runs the rebuild callback (if set) outside the git mutex.
func (gs *GitStore) triggerRebuild() {
	if gs.rebuildFn != nil {
		slog.Info("GitStore: triggering cache rebuild after merge")
		if err := gs.rebuildFn(gs.repoPath); err != nil {
			slog.Error("GitStore: cache rebuild failed", "error", err)
		}
	}
	if gs.postRebuildFn != nil {
		gs.postRebuildFn()
	}
}

// New creates a GitStore. It clones the repo if not already present,
// or pulls latest main if the clone already exists.
// If token is non-empty, it is injected into HTTPS URLs for authentication.
func New(repoURL, repoPath, token string, forge ForgeClient) (*GitStore, error) {
	gs := &GitStore{
		repoPath: repoPath,
		repoURL:  repoURL,
		forge:    forge,
	}

	cloneURL := repoURL
	if token != "" {
		cloneURL = injectToken(repoURL, token)
	}

	if _, err := os.Stat(filepath.Join(repoPath, ".git")); os.IsNotExist(err) {
		slog.Info("Cloning data repo", "url", repoURL, "path", repoPath)
		if err := gs.git("clone", cloneURL, repoPath); err != nil {
			return nil, fmt.Errorf("cloning data repo: %w", err)
		}
		// Ensure the remote URL uses the token for future push/pull
		if token != "" {
			_ = gs.gitInRepo("remote", "set-url", "origin", cloneURL)
		}
	} else {
		slog.Info("Data repo already cloned, pulling latest", "path", repoPath)
		if token != "" {
			_ = gs.gitInRepo("remote", "set-url", "origin", cloneURL)
		}
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
func (gs *GitStore) AddContribution(cs data.Contribution) error {
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

// AddProof commits a result and proof file to the contribution branch.
func (gs *GitStore) AddProof(r data.Proof) error {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("contrib/%s", r.ContributionID)

	if err := gs.checkoutBranch(branch); err != nil {
		return err
	}

	dir := filepath.Join("contributions", r.ContributionID)

	// Write result JSON
	resultPath := filepath.Join(dir, "proofs", r.ConjectureID+".json")
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
func (gs *GitStore) FinalizeContribution(id string, cs data.Contribution) (string, error) {
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
	prURL, err := func() (string, error) {
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

		return gs.forge.CreatePR(
			branch, "main",
			fmt.Sprintf("Contribution: %s", id),
			fmt.Sprintf("Sealed contribution `%s` with NFT metadata.", id),
		)
	}()
	if err != nil {
		return "", fmt.Errorf("creating PR: %w", err)
	}

	gs.triggerRebuild()
	return prURL, nil
}

// ── Certificate operations ──

// AddCertificate creates a branch and commits the certificate summary.
func (gs *GitStore) AddCertificate(cs data.Certificate) (string, error) {
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
	prURL, err := func() (string, error) {
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

		return gs.forge.CreatePR(
			branch, "main",
			fmt.Sprintf("Certificate: %s", id),
			fmt.Sprintf("Sealed certificate `%s` with NFT metadata.", id),
		)
	}()
	if err != nil {
		return "", fmt.Errorf("creating PR: %w", err)
	}

	gs.triggerRebuild()
	return prURL, nil
}

// ── Conjecture operations ──

// ConjectureSubmitResult holds all info needed by the submitter NFT flow.
type ConjectureSubmitResult struct {
	PRUrl     string
	CommitSHA string
}

// AddConjectures creates a branch, writes conjecture JSON files, commits, and creates a PR.
// Returns the PR URL and the commit SHA.
func (gs *GitStore) AddConjectures(conjectures []data.Conjecture, batchID string) (*ConjectureSubmitResult, error) {
	result, err := func() (*ConjectureSubmitResult, error) {
		gs.mu.Lock()
		defer gs.mu.Unlock()

		branch := fmt.Sprintf("conj/%s", batchID)

		if err := gs.createBranch(branch); err != nil {
			return nil, err
		}

		for _, c := range conjectures {
			path := filepath.Join("conjectures", c.ID+".toml")
			if err := gs.writeTOML(path, c); err != nil {
				return nil, err
			}
		}

		msg := fmt.Sprintf("Add %d conjectures (batch %s)", len(conjectures), batchID)
		if err := gs.commitAndPush(branch, msg); err != nil {
			return nil, err
		}

		sha, err := gs.getHeadSHA()
		if err != nil {
			return nil, err
		}

		prURL, err := gs.forge.CreatePR(
			branch, "main",
			fmt.Sprintf("Conjectures: batch %s (%d)", batchID, len(conjectures)),
			msg,
		)
		if err != nil {
			return nil, fmt.Errorf("creating PR: %w", err)
		}

		return &ConjectureSubmitResult{PRUrl: prURL, CommitSHA: sha}, nil
	}()
	if err != nil {
		return nil, err
	}

	gs.triggerRebuild()
	return result, nil
}

// SealConjecturePackage writes nft_metadata.json to the conj/{batchID} branch, commits, pushes, and returns the PR URL.
func (gs *GitStore) SealConjecturePackage(batchID string, nftMetadata any) (string, error) {
	prURL, err := func() (string, error) {
		gs.mu.Lock()
		defer gs.mu.Unlock()

		branch := fmt.Sprintf("conj/%s", batchID)

		if err := gs.checkoutBranch(branch); err != nil {
			return "", err
		}

		path := filepath.Join("conjectures", "nft_metadata_"+batchID+".json")
		if err := gs.writeJSON(path, nftMetadata); err != nil {
			return "", err
		}

		if err := gs.commitAndPush(branch, fmt.Sprintf("Seal conjecture batch %s with NFT metadata", batchID)); err != nil {
			return "", err
		}

		// The PR already exists from AddConjectures; just return a reference.
		// For forges that support it, we could update the PR. For now, return the branch name.
		prURL, err := gs.forge.CreatePR(
			branch, "main",
			fmt.Sprintf("Conjectures: batch %s (sealed)", batchID),
			fmt.Sprintf("Sealed conjecture batch `%s` with submitter NFT metadata.", batchID),
		)
		if err != nil {
			// PR may already exist (e.g. local forge), which is fine
			slog.Warn("SealConjecturePackage: CreatePR returned error (may already exist)", "error", err)
			return "", nil
		}

		return prURL, nil
	}()
	if err != nil {
		return "", err
	}

	gs.triggerRebuild()
	return prURL, nil
}

// ── Exposition operations ──

// AddExposition creates a branch and commits the exposition summary.
func (gs *GitStore) AddExposition(ex data.Exposition) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("expo/%s", ex.ExpositionID)
	dir := filepath.Join("expositions", ex.ExpositionID)

	if err := gs.createBranch(branch); err != nil {
		return "", err
	}

	if err := gs.writeJSON(filepath.Join(dir, "summary.json"), ex); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Add exposition %s", ex.ExpositionID)); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	return sha, nil
}

// SealExposition writes nft_metadata.json, commits, pushes, and creates a PR.
func (gs *GitStore) SealExposition(id string, nftMetadata any) (string, error) {
	prURL, err := func() (string, error) {
		gs.mu.Lock()
		defer gs.mu.Unlock()

		branch := fmt.Sprintf("expo/%s", id)

		if err := gs.checkoutBranch(branch); err != nil {
			return "", err
		}

		dir := filepath.Join("expositions", id)
		if err := gs.writeJSON(filepath.Join(dir, "nft_metadata.json"), nftMetadata); err != nil {
			return "", err
		}

		if err := gs.commitAndPush(branch, fmt.Sprintf("Seal exposition %s with NFT metadata", id)); err != nil {
			return "", err
		}

		return gs.forge.CreatePR(
			branch, "main",
			fmt.Sprintf("Exposition: %s", id),
			fmt.Sprintf("Sealed exposition `%s` with NFT metadata.", id),
		)
	}()
	if err != nil {
		return "", fmt.Errorf("creating PR: %w", err)
	}

	gs.triggerRebuild()
	return prURL, nil
}

// ── Lesson operations ──

// AddLesson creates a branch and commits the lesson as lesson.md with YAML frontmatter.
// Also generates an initial CREDITS.toml crediting the author.
func (gs *GitStore) AddLesson(l data.Lesson) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("lesson/%s", l.LessonID)
	dir := filepath.Join("lessons", l.LessonID)

	if err := gs.createBranch(branch); err != nil {
		return "", err
	}

	if err := gs.writeLessonMD(filepath.Join(dir, "lesson.md"), l); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Add lesson %s", l.LessonID)); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	// Generate initial CREDITS.toml
	credits := initialCredits(l.AuthorUsername, sha)
	if err := gs.writeCredits(filepath.Join(dir, "CREDITS.toml"), credits); err != nil {
		slog.Warn("AddLesson: failed to write CREDITS.toml", "error", err)
	} else {
		_ = gs.commitAndPush(branch, fmt.Sprintf("Add CREDITS.toml for lesson %s", l.LessonID))
		sha, _ = gs.getHeadSHA()
	}

	return sha, nil
}

// UpdateLesson overwrites the lesson on its branch.
// If the updating user is not already in CREDITS.toml, they are added as a contributor.
func (gs *GitStore) UpdateLesson(id string, l data.Lesson) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("lesson/%s", id)
	dir := filepath.Join("lessons", id)

	if err := gs.checkoutBranch(branch); err != nil {
		// Branch may not exist yet if lesson was merged to main; create it
		if err2 := gs.createBranch(branch); err2 != nil {
			return "", err
		}
	}

	if err := gs.writeLessonMD(filepath.Join(dir, "lesson.md"), l); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Update lesson %s", id)); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	// Update CREDITS.toml — add updating user as contributor if not present
	creditsPath := filepath.Join(dir, "CREDITS.toml")
	if credits := gs.readCredits(creditsPath); credits != nil && l.AuthorUsername != "" {
		ensureContributor(credits, l.AuthorUsername, sha)
		if err := gs.writeCredits(creditsPath, credits); err == nil {
			_ = gs.commitAndPush(branch, fmt.Sprintf("Update CREDITS.toml for lesson %s", id))
			sha, _ = gs.getHeadSHA()
		}
	}

	return sha, nil
}

// ── Series operations ──

// AddSeries creates a branch and commits the series as series.md with YAML frontmatter.
// Also generates an initial CREDITS.toml crediting the author.
func (gs *GitStore) AddSeries(s data.Series) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("series/%s", s.SeriesID)
	dir := filepath.Join("series", s.SeriesID)

	if err := gs.createBranch(branch); err != nil {
		return "", err
	}

	if err := gs.writeSeriesMD(filepath.Join(dir, "series.md"), s); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Add series %s", s.SeriesID)); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	// Generate initial CREDITS.toml
	credits := initialCredits(s.AuthorUsername, sha)
	if err := gs.writeCredits(filepath.Join(dir, "CREDITS.toml"), credits); err != nil {
		slog.Warn("AddSeries: failed to write CREDITS.toml", "error", err)
	} else {
		_ = gs.commitAndPush(branch, fmt.Sprintf("Add CREDITS.toml for series %s", s.SeriesID))
		sha, _ = gs.getHeadSHA()
	}

	return sha, nil
}

// UpdateSeries overwrites the series on its branch.
// If the updating user is not already in CREDITS.toml, they are added as a contributor.
func (gs *GitStore) UpdateSeries(id string, s data.Series) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("series/%s", id)
	dir := filepath.Join("series", id)

	if err := gs.checkoutBranch(branch); err != nil {
		if err2 := gs.createBranch(branch); err2 != nil {
			return "", err
		}
	}

	if err := gs.writeSeriesMD(filepath.Join(dir, "series.md"), s); err != nil {
		return "", err
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Update series %s", id)); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	// Update CREDITS.toml — add updating user as contributor if not present
	creditsPath := filepath.Join(dir, "CREDITS.toml")
	if credits := gs.readCredits(creditsPath); credits != nil && s.AuthorUsername != "" {
		ensureContributor(credits, s.AuthorUsername, sha)
		if err := gs.writeCredits(creditsPath, credits); err == nil {
			_ = gs.commitAndPush(branch, fmt.Sprintf("Update CREDITS.toml for series %s", id))
			sha, _ = gs.getHeadSHA()
		}
	}

	return sha, nil
}

// ── Edition bump ──

// EditionBump increments the edition in CREDITS.toml for a lesson or series.
// kind is "lesson" or "series". Returns the new commit SHA.
func (gs *GitStore) EditionBump(kind, id, summary string) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("%s/%s", kind, id)
	var dir string
	if kind == "lesson" {
		dir = filepath.Join("lessons", id)
	} else {
		dir = filepath.Join("series", id)
	}

	if err := gs.checkoutBranch(branch); err != nil {
		if err2 := gs.createBranch(branch); err2 != nil {
			return "", fmt.Errorf("checking out branch %s: %w", branch, err)
		}
	}

	creditsPath := filepath.Join(dir, "CREDITS.toml")
	credits := gs.readCredits(creditsPath)
	if credits == nil {
		return "", fmt.Errorf("CREDITS.toml not found for %s %s", kind, id)
	}

	// Increment edition
	credits.Edition.Current++
	today := time.Now().UTC().Format("2006-01-02")

	// Get HEAD for the commit field (before our bump commit)
	headSHA, _ := gs.getHeadSHA()

	credits.Edition.History = append(credits.Edition.History, data.EditionRecord{
		Edition: credits.Edition.Current,
		Date:    today,
		Commit:  headSHA,
		Summary: summary,
	})

	if err := gs.writeCredits(creditsPath, credits); err != nil {
		return "", fmt.Errorf("writing CREDITS.toml: %w", err)
	}

	msg := fmt.Sprintf("Bump %s %s to edition %d: %s", kind, id, credits.Edition.Current, summary)
	if err := gs.commitAndPush(branch, msg); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	return sha, nil
}

// BranchHeadSHA returns the HEAD SHA of a specific branch, or "" if the branch doesn't exist.
func (gs *GitStore) BranchHeadSHA(branch string) string {
	sha, err := gs.gitOutput("rev-parse", branch)
	if err != nil {
		return ""
	}
	return sha
}

// ── Note export ──

// NoteExport wraps notes for TOML serialization.
type NoteExport struct {
	Notes []data.Note `toml:"notes"`
}

// ExportNotesToGit writes all notes to a "notes" orphan branch in the data repo.
func (gs *GitStore) ExportNotesToGit(notes []data.Note) error {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	// Try to checkout existing notes branch; create orphan if it doesn't exist
	if err := gs.gitInRepo("checkout", "notes"); err != nil {
		if err := gs.gitInRepo("checkout", "--orphan", "notes"); err != nil {
			return fmt.Errorf("creating orphan notes branch: %w", err)
		}
		// Remove all tracked files from the orphan branch
		gs.gitInRepo("rm", "-rf", ".")
	}

	// Clear existing notes/ directory
	notesDir := filepath.Join(gs.repoPath, "notes")
	os.RemoveAll(notesDir)

	// Group notes by lesson_id
	grouped := make(map[string][]data.Note)
	for _, n := range notes {
		grouped[n.LessonID] = append(grouped[n.LessonID], n)
	}

	// Write each group as notes/{lesson_id}.toml
	for lessonID, lessonNotes := range grouped {
		export := NoteExport{Notes: lessonNotes}
		if err := gs.writeTOML(filepath.Join("notes", lessonID+".toml"), export); err != nil {
			return fmt.Errorf("writing notes for lesson %s: %w", lessonID, err)
		}
	}

	// Commit and push
	msg := fmt.Sprintf("Export notes snapshot %s", time.Now().UTC().Format(time.RFC3339))
	if err := gs.commitAndPush("notes", msg); err != nil {
		return fmt.Errorf("committing notes export: %w", err)
	}

	// Return to main branch
	if err := gs.gitInRepo("checkout", "main"); err != nil {
		slog.Warn("ExportNotesToGit: failed to checkout main after export", "error", err)
	}

	return nil
}

// ── Cache rebuild ──

// PullAndRebuild pulls latest main and calls the rebuild function.
// The rebuild func is provided by the caller (typically SQLiteStore.RebuildFromDir).
func (gs *GitStore) PullAndRebuild(rebuildFn func(repoPath string) error) error {
	if err := func() error {
		gs.mu.Lock()
		defer gs.mu.Unlock()

		if err := gs.gitInRepo("checkout", "main"); err != nil {
			return fmt.Errorf("checking out main: %w", err)
		}
		if err := gs.gitInRepo("pull", "origin", "main"); err != nil {
			return fmt.Errorf("pulling latest: %w", err)
		}
		return nil
	}(); err != nil {
		return err
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

func (gs *GitStore) writeTOML(relPath string, v any) error {
	absPath := filepath.Join(gs.repoPath, relPath)
	if err := os.MkdirAll(filepath.Dir(absPath), 0o755); err != nil {
		return fmt.Errorf("creating directory for %s: %w", relPath, err)
	}

	data, err := toml.Marshal(v)
	if err != nil {
		return fmt.Errorf("marshaling TOML for %s: %w", relPath, err)
	}

	if err := os.WriteFile(absPath, data, 0o644); err != nil {
		return fmt.Errorf("writing %s: %w", relPath, err)
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

// MainHeadSHA returns the current HEAD SHA of the main branch.
func (gs *GitStore) MainHeadSHA() string {
	sha, err := gs.gitOutput("rev-parse", "main")
	if err != nil {
		slog.Warn("MainHeadSHA: failed to get main HEAD", "error", err)
		return ""
	}
	return sha
}

func (gs *GitStore) writeLessonMD(relPath string, l data.Lesson) error {
	absPath := filepath.Join(gs.repoPath, relPath)
	if err := os.MkdirAll(filepath.Dir(absPath), 0o755); err != nil {
		return fmt.Errorf("creating directory for %s: %w", relPath, err)
	}

	mdBytes, err := data.RenderLessonFile(l)
	if err != nil {
		return fmt.Errorf("rendering lesson.md: %w", err)
	}

	if err := os.WriteFile(absPath, mdBytes, 0o644); err != nil {
		return fmt.Errorf("writing %s: %w", relPath, err)
	}
	return nil
}

func (gs *GitStore) writeSeriesMD(relPath string, s data.Series) error {
	absPath := filepath.Join(gs.repoPath, relPath)
	if err := os.MkdirAll(filepath.Dir(absPath), 0o755); err != nil {
		return fmt.Errorf("creating directory for %s: %w", relPath, err)
	}

	mdBytes, err := data.RenderSeriesFile(s)
	if err != nil {
		return fmt.Errorf("rendering series.md: %w", err)
	}

	if err := os.WriteFile(absPath, mdBytes, 0o644); err != nil {
		return fmt.Errorf("writing %s: %w", relPath, err)
	}
	return nil
}

// ── Strategy operations ──

// AddStrategy creates a branch and commits a strategy file to the repo.
func (gs *GitStore) AddStrategy(name string, content []byte) (string, error) {
	gs.mu.Lock()
	defer gs.mu.Unlock()

	branch := fmt.Sprintf("strategy/%s", name)

	if err := gs.createBranch(branch); err != nil {
		return "", err
	}

	relPath := filepath.Join("strategies", name+".md")
	absPath := filepath.Join(gs.repoPath, relPath)
	if err := os.MkdirAll(filepath.Dir(absPath), 0o755); err != nil {
		return "", fmt.Errorf("creating directory for %s: %w", relPath, err)
	}
	if err := os.WriteFile(absPath, content, 0o644); err != nil {
		return "", fmt.Errorf("writing %s: %w", relPath, err)
	}

	if err := gs.commitAndPush(branch, fmt.Sprintf("Add strategy %s", name)); err != nil {
		return "", err
	}

	sha, err := gs.getHeadSHA()
	if err != nil {
		return "", err
	}

	return sha, nil
}

// SealStrategy writes NFT metadata, commits, pushes, and creates a PR for a strategy.
func (gs *GitStore) SealStrategy(name string, nftMetadata any) (string, error) {
	prURL, err := func() (string, error) {
		gs.mu.Lock()
		defer gs.mu.Unlock()

		branch := fmt.Sprintf("strategy/%s", name)

		if err := gs.checkoutBranch(branch); err != nil {
			return "", err
		}

		relPath := filepath.Join("strategies", "nft_metadata_"+name+".json")
		if err := gs.writeJSON(relPath, nftMetadata); err != nil {
			return "", err
		}

		if err := gs.commitAndPush(branch, fmt.Sprintf("Seal strategy %s with NFT metadata", name)); err != nil {
			return "", err
		}

		return gs.forge.CreatePR(
			branch, "main",
			fmt.Sprintf("Strategy: %s", name),
			fmt.Sprintf("Sealed strategy/memory `%s` with NFT metadata.", name),
		)
	}()
	if err != nil {
		return "", fmt.Errorf("creating PR: %w", err)
	}

	gs.triggerRebuild()
	return prURL, nil
}

// injectToken embeds a token into an HTTPS git URL for authentication.
// e.g. https://github.com/org/repo.git -> https://x-access-token:TOKEN@github.com/org/repo.git
func injectToken(repoURL, token string) string {
	if strings.HasPrefix(repoURL, "https://") {
		return "https://x-access-token:" + token + "@" + strings.TrimPrefix(repoURL, "https://")
	}
	return repoURL
}
