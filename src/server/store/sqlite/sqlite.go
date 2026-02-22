package sqlite

import (
	"context"
	"database/sql"
	_ "embed"
	"encoding/json"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"

	"github.com/proof-at-home/server/src/server/data"
	_ "modernc.org/sqlite"
)

//go:embed migrations/001_initial.sql
var migrationSQL string

type SQLiteStore struct {
	db *sql.DB
}

func New(dbPath string) (*SQLiteStore, error) {
	db, err := sql.Open("sqlite", dbPath+"?_journal_mode=WAL&_busy_timeout=5000&_foreign_keys=on")
	if err != nil {
		return nil, fmt.Errorf("opening database: %w", err)
	}

	// SQLite performs best with a single writer
	db.SetMaxOpenConns(1)

	if err := db.Ping(); err != nil {
		return nil, fmt.Errorf("pinging database: %w", err)
	}

	return &SQLiteStore{db: db}, nil
}

func (s *SQLiteStore) Migrate() error {
	_, err := s.db.Exec(migrationSQL)
	if err != nil {
		return fmt.Errorf("running migration: %w", err)
	}
	slog.Info("SQLite migration completed")
	return nil
}

func (s *SQLiteStore) Ping(ctx context.Context) error {
	return s.db.PingContext(ctx)
}

func (s *SQLiteStore) Close() error {
	return s.db.Close()
}

func (s *SQLiteStore) ListProblems() []data.ProblemSummary {
	rows, err := s.db.Query(`SELECT id, title, difficulty, proof_assistant, status FROM problems ORDER BY id`)
	if err != nil {
		slog.Error("ListProblems query failed", "error", err)
		return nil
	}
	defer rows.Close()

	var summaries []data.ProblemSummary
	for rows.Next() {
		var p data.ProblemSummary
		if err := rows.Scan(&p.ID, &p.Title, &p.Difficulty, &p.ProofAssistant, &p.Status); err != nil {
			slog.Error("ListProblems scan failed", "error", err)
			continue
		}
		summaries = append(summaries, p)
	}
	return summaries
}

func (s *SQLiteStore) GetProblem(id string) (data.Problem, bool) {
	var p data.Problem
	var hints, deps sql.NullString

	err := s.db.QueryRow(
		`SELECT id, title, difficulty, proof_assistant, status, preamble, lemma_statement, hints, skeleton, dependencies
		 FROM problems WHERE id = ?`, id,
	).Scan(&p.ID, &p.Title, &p.Difficulty, &p.ProofAssistant, &p.Status,
		&p.Preamble, &p.LemmaStatement, &hints, &p.Skeleton, &deps)

	if err == sql.ErrNoRows {
		return data.Problem{}, false
	}
	if err != nil {
		slog.Error("GetProblem query failed", "error", err, "id", id)
		return data.Problem{}, false
	}

	if hints.Valid {
		json.Unmarshal([]byte(hints.String), &p.Hints)
	}
	if deps.Valid {
		p.Dependencies = json.RawMessage(deps.String)
	}

	return p, true
}

func (s *SQLiteStore) AddProblems(problems []data.Problem) []string {
	var added []string
	for _, p := range problems {
		if p.ID == "" {
			continue
		}
		if p.Status == "" {
			p.Status = "open"
		}

		hintsJSON, _ := json.Marshal(p.Hints)
		var depsJSON *string
		if p.Dependencies != nil {
			d := string(p.Dependencies)
			depsJSON = &d
		}

		res, err := s.db.Exec(
			`INSERT INTO problems (id, title, difficulty, proof_assistant, status, preamble, lemma_statement, hints, skeleton, dependencies)
			 VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
			 ON CONFLICT (id) DO NOTHING`,
			p.ID, p.Title, p.Difficulty, p.ProofAssistant, p.Status,
			p.Preamble, p.LemmaStatement, string(hintsJSON), p.Skeleton, depsJSON,
		)
		if err != nil {
			slog.Error("AddProblems insert failed", "error", err, "id", p.ID)
			continue
		}

		rows, _ := res.RowsAffected()
		if rows > 0 {
			added = append(added, p.ID)
		}
	}
	return added
}

func (s *SQLiteStore) AddResult(r data.ProofResult) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddResult begin tx failed", "error", err)
		return
	}
	defer tx.Rollback()

	successInt := 0
	if r.Success {
		successInt = 1
	}

	_, err = tx.Exec(
		`INSERT INTO proof_results (problem_id, username, success, proof_script, cost_usd, attempts, error_output)
		 VALUES (?, ?, ?, ?, ?, ?, ?)`,
		r.ProblemID, r.Username, successInt, r.ProofScript, r.CostUSD, r.Attempts, r.ErrorOutput,
	)
	if err != nil {
		slog.Error("AddResult insert failed", "error", err)
		return
	}

	if r.Success {
		_, err = tx.Exec(`UPDATE problems SET status = 'proved' WHERE id = ?`, r.ProblemID)
		if err != nil {
			slog.Error("AddResult update status failed", "error", err)
			return
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddResult commit failed", "error", err)
	}
}

func (s *SQLiteStore) AddSession(ss data.SessionSummary) {
	problemIDsJSON, _ := json.Marshal(ss.ProblemIDs)
	reviewedByJSON, _ := json.Marshal(ss.ReviewedBy)
	var nftJSON *string
	if ss.NFTMetadata != nil {
		b, _ := json.Marshal(ss.NFTMetadata)
		n := string(b)
		nftJSON = &n
	}

	_, err := s.db.Exec(
		`INSERT INTO sessions (session_id, username, problems_attempted, problems_proved, total_cost_usd,
		 archive_sha256, nft_metadata, proof_assistant, problem_ids, archive_path, proof_status, reviewed_by)
		 VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
		 ON CONFLICT (session_id) DO UPDATE SET
		   problems_attempted = excluded.problems_attempted,
		   problems_proved = excluded.problems_proved,
		   total_cost_usd = excluded.total_cost_usd,
		   archive_sha256 = excluded.archive_sha256,
		   nft_metadata = excluded.nft_metadata,
		   proof_assistant = excluded.proof_assistant,
		   problem_ids = excluded.problem_ids,
		   archive_path = excluded.archive_path,
		   proof_status = excluded.proof_status,
		   reviewed_by = excluded.reviewed_by`,
		ss.SessionID, ss.Username, ss.ProblemsAttempted, ss.ProblemsProved,
		ss.TotalCostUSD, ss.ArchiveSHA256, nftJSON, ss.ProofAssistant,
		string(problemIDsJSON), ss.ArchivePath, ss.ProofStatus, string(reviewedByJSON),
	)
	if err != nil {
		slog.Error("AddSession insert failed", "error", err)
	}
}

func (s *SQLiteStore) ListReviewPackages() []data.ReviewPackageInfo {
	rows, err := s.db.Query(
		`SELECT session_id, username, proof_assistant, problem_ids, archive_sha256, proof_status, reviewed_by
		 FROM sessions ORDER BY created_at`)
	if err != nil {
		slog.Error("ListReviewPackages query failed", "error", err)
		return nil
	}
	defer rows.Close()

	var packages []data.ReviewPackageInfo
	for rows.Next() {
		var sessionID, username, proofAssistant, archiveSHA256, proofStatus string
		var problemIDsStr, reviewedByStr string

		if err := rows.Scan(&sessionID, &username, &proofAssistant, &problemIDsStr, &archiveSHA256, &proofStatus, &reviewedByStr); err != nil {
			slog.Error("ListReviewPackages scan failed", "error", err)
			continue
		}

		var problemIDs []string
		var reviewedBy []string
		json.Unmarshal([]byte(problemIDsStr), &problemIDs)
		json.Unmarshal([]byte(reviewedByStr), &reviewedBy)

		if len(problemIDs) == 0 {
			// Fallback: scan results for this user
			resultRows, err := s.db.Query(
				`SELECT DISTINCT problem_id FROM proof_results WHERE username = ? AND success = 1`, username)
			if err == nil {
				for resultRows.Next() {
					var pid string
					if resultRows.Scan(&pid) == nil {
						problemIDs = append(problemIDs, pid)
					}
				}
				resultRows.Close()
			}
		}

		if proofAssistant == "" {
			proofAssistant = "rocq"
		}

		packages = append(packages, data.ReviewPackageInfo{
			ProverSessionID: sessionID,
			ProverUsername:  username,
			ProofAssistant:  proofAssistant,
			ProblemIDs:      problemIDs,
			ArchiveURL:      fmt.Sprintf("/review-packages/%s/archive", sessionID),
			ArchiveSHA256:   archiveSHA256,
			ProofStatus:     proofStatus,
			ReviewedBy:      reviewedBy,
		})
	}
	return packages
}

func (s *SQLiteStore) GetArchivePath(sessionID string) (string, bool) {
	var path string
	err := s.db.QueryRow(`SELECT archive_path FROM sessions WHERE session_id = ?`, sessionID).Scan(&path)
	if err != nil {
		return "", false
	}
	return path, true
}

func (s *SQLiteStore) AddReview(r data.ReviewSummary) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddReview begin tx failed", "error", err)
		return
	}
	defer tx.Rollback()

	rankingsJSON, _ := json.Marshal(r.PackageRankings)
	var nftJSON *string
	if r.NFTMetadata != nil {
		b, _ := json.Marshal(r.NFTMetadata)
		n := string(b)
		nftJSON = &n
	}

	_, err = tx.Exec(
		`INSERT INTO reviews (review_id, reviewer_username, packages_reviewed, problems_compared, package_rankings, recommendation, archive_sha256, nft_metadata)
		 VALUES (?, ?, ?, ?, ?, ?, ?, ?)`,
		r.ReviewID, r.ReviewerUsername, r.PackagesReviewed, r.ProblemsCompared,
		string(rankingsJSON), r.Recommendation, r.ArchiveSHA256, nftJSON,
	)
	if err != nil {
		slog.Error("AddReview insert failed", "error", err)
		return
	}

	// Update reviewed_by for each session referenced in the review
	for _, pr := range r.PackageRankings {
		// Read current reviewed_by, add reviewer, write back
		var currentJSON string
		err := tx.QueryRow(`SELECT reviewed_by FROM sessions WHERE session_id = ?`, pr.ProverSessionID).Scan(&currentJSON)
		if err != nil {
			slog.Error("AddReview read reviewed_by failed", "error", err, "session_id", pr.ProverSessionID)
			continue
		}

		var current []string
		json.Unmarshal([]byte(currentJSON), &current)

		// Add reviewer if not already present
		found := false
		for _, reviewer := range current {
			if reviewer == r.ReviewerUsername {
				found = true
				break
			}
		}
		if !found {
			current = append(current, r.ReviewerUsername)
			updatedJSON, _ := json.Marshal(current)
			_, err = tx.Exec(`UPDATE sessions SET reviewed_by = ? WHERE session_id = ?`,
				string(updatedJSON), pr.ProverSessionID)
			if err != nil {
				slog.Error("AddReview update reviewed_by failed", "error", err, "session_id", pr.ProverSessionID)
			}
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddReview commit failed", "error", err)
	}
}

// LoadProblems loads problem JSON files from a directory into the database.
func (s *SQLiteStore) LoadProblems(dir string) error {
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

		s.AddProblems([]data.Problem{p})
	}
	return nil
}

// LoadSeedSessions loads seed session JSON files from a directory.
func (s *SQLiteStore) LoadSeedSessions(dir string) error {
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

		if ss.ArchivePath != "" && !filepath.IsAbs(ss.ArchivePath) {
			ss.ArchivePath = filepath.Join(dir, ss.ArchivePath)
		}

		s.AddSession(ss)
	}
	return nil
}
