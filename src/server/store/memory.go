package store

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sync"

	"github.com/proof-at-home/server/src/server/data"
)

type MemoryStore struct {
	mu            sync.RWMutex
	conjectures   map[string]data.Conjecture
	order         []string
	certificates  []data.Certificate
	contributions []data.ContributionSummary
	reviews       []data.ReviewSummary
}

func NewMemoryStore() *MemoryStore {
	return &MemoryStore{
		conjectures: make(map[string]data.Conjecture),
	}
}

func (s *MemoryStore) LoadConjectures(dir string) error {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return fmt.Errorf("reading conjectures dir: %w", err)
	}

	for _, entry := range entries {
		if entry.IsDir() || filepath.Ext(entry.Name()) != ".json" {
			continue
		}
		path := filepath.Join(dir, entry.Name())
		raw, err := os.ReadFile(path)
		if err != nil {
			return fmt.Errorf("reading %s: %w", path, err)
		}

		var p data.Conjecture
		if err := json.Unmarshal(raw, &p); err != nil {
			return fmt.Errorf("parsing %s: %w", path, err)
		}

		if p.Status == "" {
			p.Status = "open"
		}

		s.mu.Lock()
		s.conjectures[p.ID] = p
		s.order = append(s.order, p.ID)
		s.mu.Unlock()
	}

	return nil
}

// AddConjectures inserts conjectures into the store, skipping duplicates.
// Returns the IDs of newly added conjectures.
func (s *MemoryStore) AddConjectures(conjectures []data.Conjecture) []string {
	s.mu.Lock()
	defer s.mu.Unlock()

	var added []string
	for _, p := range conjectures {
		if p.ID == "" {
			continue
		}
		if _, exists := s.conjectures[p.ID]; exists {
			continue
		}
		if p.Status == "" {
			p.Status = "open"
		}
		s.conjectures[p.ID] = p
		s.order = append(s.order, p.ID)
		added = append(added, p.ID)
	}
	return added
}

func (s *MemoryStore) ListConjectures() []data.ConjectureSummary {
	s.mu.RLock()
	defer s.mu.RUnlock()

	summaries := make([]data.ConjectureSummary, 0, len(s.order))
	for _, id := range s.order {
		p := s.conjectures[id]
		summaries = append(summaries, data.ConjectureSummary{
			ID:         p.ID,
			Title:      p.Title,
			Difficulty: p.Difficulty,
			Prover:     p.Prover,
			Status:     p.Status,
		})
	}
	return summaries
}

func (s *MemoryStore) GetConjecture(id string) (data.Conjecture, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	p, ok := s.conjectures[id]
	return p, ok
}

func (s *MemoryStore) AddCertificate(r data.Certificate) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.certificates = append(s.certificates, r)

	if r.Success {
		if p, ok := s.conjectures[r.ConjectureID]; ok {
			p.Status = "proved"
			s.conjectures[r.ConjectureID] = p
		}
	}
}

func (s *MemoryStore) AddContribution(cs data.ContributionSummary) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.contributions = append(s.contributions, cs)
}

// ── Review methods ──

// ListReviewPackages returns all submitted contributions as reviewable packages.
func (s *MemoryStore) ListReviewPackages() []data.ReviewPackageInfo {
	s.mu.RLock()
	defer s.mu.RUnlock()

	packages := make([]data.ReviewPackageInfo, 0, len(s.contributions))
	for _, cs := range s.contributions {
		// Build conjecture IDs from successful results for this contribution
		conjectureIDs := cs.ConjectureIDs
		if len(conjectureIDs) == 0 {
			// Fallback: scan results for this user
			seen := map[string]bool{}
			for _, r := range s.certificates {
				if r.Username == cs.Username && r.Success {
					if !seen[r.ConjectureID] {
						conjectureIDs = append(conjectureIDs, r.ConjectureID)
						seen[r.ConjectureID] = true
					}
				}
			}
		}

		prover := cs.Prover
		if prover == "" {
			prover = "rocq"
		}

		packages = append(packages, data.ReviewPackageInfo{
			ProverContributionID: cs.ContributionID,
			ProverUsername:       cs.Username,
			Prover:               prover,
			ConjectureIDs:        conjectureIDs,
			ArchiveURL:           fmt.Sprintf("/review-packages/%s/archive", cs.ContributionID),
			ArchiveSHA256:        cs.ArchiveSHA256,
			ProofStatus:          cs.ProofStatus,
			ReviewedBy:           cs.ReviewedBy,
		})
	}
	return packages
}

// GetArchivePath returns the archive file path for a given contribution ID.
func (s *MemoryStore) GetArchivePath(contributionID string) (string, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()

	for _, cs := range s.contributions {
		if cs.ContributionID == contributionID {
			return cs.ArchivePath, true
		}
	}
	return "", false
}

// AddReview stores a submitted review and updates reviewed_by on affected contributions.
func (s *MemoryStore) AddReview(r data.ReviewSummary) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.reviews = append(s.reviews, r)

	// Update reviewed_by for each contribution referenced in the review's package rankings
	for _, pr := range r.PackageRankings {
		for i, cs := range s.contributions {
			if cs.ContributionID == pr.ProverContributionID {
				// Add reviewer if not already present
				found := false
				for _, reviewer := range cs.ReviewedBy {
					if reviewer == r.ReviewerUsername {
						found = true
						break
					}
				}
				if !found {
					s.contributions[i].ReviewedBy = append(s.contributions[i].ReviewedBy, r.ReviewerUsername)
				}
				break
			}
		}
	}
}

// LoadSeedContributions loads seed contribution JSON files from a directory.
// Each file should be a JSON-encoded ContributionSummary with archive_path pointing
// to a .tar.gz file (absolute or relative to the seed directory).
func (s *MemoryStore) LoadSeedContributions(dir string) error {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return fmt.Errorf("reading seed dir: %w", err)
	}

	for _, entry := range entries {
		if entry.IsDir() || filepath.Ext(entry.Name()) != ".json" {
			continue
		}
		path := filepath.Join(dir, entry.Name())
		raw, err := os.ReadFile(path)
		if err != nil {
			return fmt.Errorf("reading %s: %w", path, err)
		}

		var cs data.ContributionSummary
		if err := json.Unmarshal(raw, &cs); err != nil {
			return fmt.Errorf("parsing %s: %w", path, err)
		}

		// Resolve relative archive_path against the seed directory
		if cs.ArchivePath != "" && !filepath.IsAbs(cs.ArchivePath) {
			cs.ArchivePath = filepath.Join(dir, cs.ArchivePath)
		}

		s.mu.Lock()
		s.contributions = append(s.contributions, cs)
		s.mu.Unlock()
	}

	return nil
}
