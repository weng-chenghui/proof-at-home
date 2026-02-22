package postgres

import (
	"context"
	"database/sql"
	_ "embed"
	"encoding/json"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"time"

	_ "github.com/lib/pq"
	"github.com/proof-at-home/server/src/server/data"
)

//go:embed migrations/001_initial.sql
var migrationSQL string

type PostgresStore struct {
	db *sql.DB
}

func New(databaseURL string) (*PostgresStore, error) {
	db, err := sql.Open("postgres", databaseURL)
	if err != nil {
		return nil, fmt.Errorf("opening database: %w", err)
	}

	db.SetMaxOpenConns(25)
	db.SetMaxIdleConns(5)
	db.SetConnMaxLifetime(5 * time.Minute)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	if err := db.PingContext(ctx); err != nil {
		return nil, fmt.Errorf("pinging database: %w", err)
	}

	return &PostgresStore{db: db}, nil
}

func (s *PostgresStore) Migrate() error {
	_, err := s.db.Exec(migrationSQL)
	if err != nil {
		return fmt.Errorf("running migration: %w", err)
	}
	slog.Info("Database migration completed")
	return nil
}

func (s *PostgresStore) Ping(ctx context.Context) error {
	return s.db.PingContext(ctx)
}

func (s *PostgresStore) Close() error {
	return s.db.Close()
}

func (s *PostgresStore) ListProblems() []data.ProblemSummary {
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

func (s *PostgresStore) GetProblem(id string) (data.Problem, bool) {
	var p data.Problem
	var hints, deps []byte

	err := s.db.QueryRow(
		`SELECT id, title, difficulty, proof_assistant, status, preamble, lemma_statement, hints, skeleton, dependencies
		 FROM problems WHERE id = $1`, id,
	).Scan(&p.ID, &p.Title, &p.Difficulty, &p.ProofAssistant, &p.Status,
		&p.Preamble, &p.LemmaStatement, &hints, &p.Skeleton, &deps)

	if err == sql.ErrNoRows {
		return data.Problem{}, false
	}
	if err != nil {
		slog.Error("GetProblem query failed", "error", err, "id", id)
		return data.Problem{}, false
	}

	if hints != nil {
		json.Unmarshal(hints, &p.Hints)
	}
	if deps != nil {
		p.Dependencies = json.RawMessage(deps)
	}

	return p, true
}

func (s *PostgresStore) AddProblems(problems []data.Problem) []string {
	var added []string
	for _, p := range problems {
		if p.ID == "" {
			continue
		}
		if p.Status == "" {
			p.Status = "open"
		}

		hintsJSON, _ := json.Marshal(p.Hints)
		var depsJSON []byte
		if p.Dependencies != nil {
			depsJSON = []byte(p.Dependencies)
		}

		res, err := s.db.Exec(
			`INSERT INTO problems (id, title, difficulty, proof_assistant, status, preamble, lemma_statement, hints, skeleton, dependencies)
			 VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
			 ON CONFLICT (id) DO NOTHING`,
			p.ID, p.Title, p.Difficulty, p.ProofAssistant, p.Status,
			p.Preamble, p.LemmaStatement, hintsJSON, p.Skeleton, depsJSON,
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

func (s *PostgresStore) AddResult(r data.ProofResult) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddResult begin tx failed", "error", err)
		return
	}
	defer tx.Rollback()

	_, err = tx.Exec(
		`INSERT INTO proof_results (problem_id, username, success, proof_script, cost_usd, attempts, error_output)
		 VALUES ($1, $2, $3, $4, $5, $6, $7)`,
		r.ProblemID, r.Username, r.Success, r.ProofScript, r.CostUSD, r.Attempts, r.ErrorOutput,
	)
	if err != nil {
		slog.Error("AddResult insert failed", "error", err)
		return
	}

	if r.Success {
		_, err = tx.Exec(`UPDATE problems SET status = 'proved' WHERE id = $1`, r.ProblemID)
		if err != nil {
			slog.Error("AddResult update status failed", "error", err)
			return
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddResult commit failed", "error", err)
	}
}

func (s *PostgresStore) AddSession(ss data.SessionSummary) {
	problemIDsJSON, _ := json.Marshal(ss.ProblemIDs)
	reviewedByJSON, _ := json.Marshal(ss.ReviewedBy)
	var nftJSON []byte
	if ss.NFTMetadata != nil {
		nftJSON, _ = json.Marshal(ss.NFTMetadata)
	}

	_, err := s.db.Exec(
		`INSERT INTO sessions (session_id, username, problems_attempted, problems_proved, total_cost_usd,
		 archive_sha256, nft_metadata, proof_assistant, problem_ids, archive_path, proof_status, reviewed_by)
		 VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12)
		 ON CONFLICT (session_id) DO UPDATE SET
		   problems_attempted = EXCLUDED.problems_attempted,
		   problems_proved = EXCLUDED.problems_proved,
		   total_cost_usd = EXCLUDED.total_cost_usd,
		   archive_sha256 = EXCLUDED.archive_sha256,
		   nft_metadata = EXCLUDED.nft_metadata,
		   proof_assistant = EXCLUDED.proof_assistant,
		   problem_ids = EXCLUDED.problem_ids,
		   archive_path = EXCLUDED.archive_path,
		   proof_status = EXCLUDED.proof_status,
		   reviewed_by = EXCLUDED.reviewed_by`,
		ss.SessionID, ss.Username, ss.ProblemsAttempted, ss.ProblemsProved,
		ss.TotalCostUSD, ss.ArchiveSHA256, nftJSON, ss.ProofAssistant,
		problemIDsJSON, ss.ArchivePath, ss.ProofStatus, reviewedByJSON,
	)
	if err != nil {
		slog.Error("AddSession insert failed", "error", err)
	}
}

func (s *PostgresStore) ListReviewPackages() []data.ReviewPackageInfo {
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
		var problemIDsJSON, reviewedByJSON []byte

		if err := rows.Scan(&sessionID, &username, &proofAssistant, &problemIDsJSON, &archiveSHA256, &proofStatus, &reviewedByJSON); err != nil {
			slog.Error("ListReviewPackages scan failed", "error", err)
			continue
		}

		var problemIDs []string
		var reviewedBy []string
		json.Unmarshal(problemIDsJSON, &problemIDs)
		json.Unmarshal(reviewedByJSON, &reviewedBy)

		if len(problemIDs) == 0 {
			// Fallback: scan results for this user
			resultRows, err := s.db.Query(
				`SELECT DISTINCT problem_id FROM proof_results WHERE username = $1 AND success = true`, username)
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

func (s *PostgresStore) GetArchivePath(sessionID string) (string, bool) {
	var path string
	err := s.db.QueryRow(`SELECT archive_path FROM sessions WHERE session_id = $1`, sessionID).Scan(&path)
	if err != nil {
		return "", false
	}
	return path, true
}

func (s *PostgresStore) AddReview(r data.ReviewSummary) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddReview begin tx failed", "error", err)
		return
	}
	defer tx.Rollback()

	rankingsJSON, _ := json.Marshal(r.PackageRankings)
	var nftJSON []byte
	if r.NFTMetadata != nil {
		nftJSON, _ = json.Marshal(r.NFTMetadata)
	}

	_, err = tx.Exec(
		`INSERT INTO reviews (review_id, reviewer_username, packages_reviewed, problems_compared, package_rankings, recommendation, archive_sha256, nft_metadata)
		 VALUES ($1, $2, $3, $4, $5, $6, $7, $8)`,
		r.ReviewID, r.ReviewerUsername, r.PackagesReviewed, r.ProblemsCompared,
		rankingsJSON, r.Recommendation, r.ArchiveSHA256, nftJSON,
	)
	if err != nil {
		slog.Error("AddReview insert failed", "error", err)
		return
	}

	// Update reviewed_by for each session referenced in the review
	for _, pr := range r.PackageRankings {
		_, err = tx.Exec(
			`UPDATE sessions SET reviewed_by = (
				SELECT jsonb_agg(DISTINCT val)
				FROM (
					SELECT jsonb_array_elements_text(reviewed_by) AS val
					UNION
					SELECT $1
				) sub
			) WHERE session_id = $2`,
			r.ReviewerUsername, pr.ProverSessionID,
		)
		if err != nil {
			slog.Error("AddReview update reviewed_by failed", "error", err, "session_id", pr.ProverSessionID)
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddReview commit failed", "error", err)
	}
}

// LoadProblems loads problem JSON files from a directory into the database.
func (s *PostgresStore) LoadProblems(dir string) error {
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
func (s *PostgresStore) LoadSeedSessions(dir string) error {
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
