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
	mu       sync.RWMutex
	problems map[string]data.Problem
	order    []string
	results  []data.ProofResult
	sessions []data.SessionSummary
	reviews  []data.ReviewSummary
}

func NewMemoryStore() *MemoryStore {
	return &MemoryStore{
		problems: make(map[string]data.Problem),
	}
}

func (s *MemoryStore) LoadProblems(dir string) error {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return fmt.Errorf("reading problems dir: %w", err)
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

		var p data.Problem
		if err := json.Unmarshal(raw, &p); err != nil {
			return fmt.Errorf("parsing %s: %w", path, err)
		}

		if p.Status == "" {
			p.Status = "open"
		}

		s.mu.Lock()
		s.problems[p.ID] = p
		s.order = append(s.order, p.ID)
		s.mu.Unlock()
	}

	return nil
}

func (s *MemoryStore) ListProblems() []data.ProblemSummary {
	s.mu.RLock()
	defer s.mu.RUnlock()

	summaries := make([]data.ProblemSummary, 0, len(s.order))
	for _, id := range s.order {
		p := s.problems[id]
		summaries = append(summaries, data.ProblemSummary{
			ID:             p.ID,
			Title:          p.Title,
			Difficulty:     p.Difficulty,
			ProofAssistant: p.ProofAssistant,
			Status:         p.Status,
		})
	}
	return summaries
}

func (s *MemoryStore) GetProblem(id string) (data.Problem, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	p, ok := s.problems[id]
	return p, ok
}

func (s *MemoryStore) AddResult(r data.ProofResult) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.results = append(s.results, r)

	if r.Success {
		if p, ok := s.problems[r.ProblemID]; ok {
			p.Status = "proved"
			s.problems[r.ProblemID] = p
		}
	}
}

func (s *MemoryStore) AddSession(ss data.SessionSummary) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.sessions = append(s.sessions, ss)
}

// ── Review methods ──

// ListReviewPackages returns all submitted sessions as reviewable packages.
func (s *MemoryStore) ListReviewPackages() []data.ReviewPackageInfo {
	s.mu.RLock()
	defer s.mu.RUnlock()

	packages := make([]data.ReviewPackageInfo, 0, len(s.sessions))
	for _, ss := range s.sessions {
		// Build problem IDs from successful results for this session
		problemIDs := ss.ProblemIDs
		if len(problemIDs) == 0 {
			// Fallback: scan results for this user
			seen := map[string]bool{}
			for _, r := range s.results {
				if r.Username == ss.Username && r.Success {
					if !seen[r.ProblemID] {
						problemIDs = append(problemIDs, r.ProblemID)
						seen[r.ProblemID] = true
					}
				}
			}
		}

		proofAssistant := ss.ProofAssistant
		if proofAssistant == "" {
			proofAssistant = "coq"
		}

		packages = append(packages, data.ReviewPackageInfo{
			ProverSessionID: ss.SessionID,
			ProverUsername:  ss.Username,
			ProofAssistant:  proofAssistant,
			ProblemIDs:      problemIDs,
			ArchiveURL:      fmt.Sprintf("/review-packages/%s/archive", ss.SessionID),
			ArchiveSHA256:   ss.ArchiveSHA256,
		})
	}
	return packages
}

// GetArchivePath returns the archive file path for a given session ID.
func (s *MemoryStore) GetArchivePath(sessionID string) (string, bool) {
	s.mu.RLock()
	defer s.mu.RUnlock()

	for _, ss := range s.sessions {
		if ss.SessionID == sessionID {
			return ss.ArchivePath, true
		}
	}
	return "", false
}

// AddReview stores a submitted review.
func (s *MemoryStore) AddReview(r data.ReviewSummary) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.reviews = append(s.reviews, r)
}

// LoadSeedSessions loads seed session JSON files from a directory.
// Each file should be a JSON-encoded SessionSummary with archive_path pointing
// to a .tar.gz file (absolute or relative to the seed directory).
func (s *MemoryStore) LoadSeedSessions(dir string) error {
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

		var ss data.SessionSummary
		if err := json.Unmarshal(raw, &ss); err != nil {
			return fmt.Errorf("parsing %s: %w", path, err)
		}

		// Resolve relative archive_path against the seed directory
		if ss.ArchivePath != "" && !filepath.IsAbs(ss.ArchivePath) {
			ss.ArchivePath = filepath.Join(dir, ss.ArchivePath)
		}

		s.mu.Lock()
		s.sessions = append(s.sessions, ss)
		s.mu.Unlock()
	}

	return nil
}
