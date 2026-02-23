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

func (s *SQLiteStore) ListConjectures() []data.ConjectureSummary {
	rows, err := s.db.Query(`SELECT id, title, difficulty, prover, status FROM conjectures ORDER BY id`)
	if err != nil {
		slog.Error("ListConjectures query failed", "error", err)
		return nil
	}
	defer rows.Close()

	var summaries []data.ConjectureSummary
	for rows.Next() {
		var p data.ConjectureSummary
		if err := rows.Scan(&p.ID, &p.Title, &p.Difficulty, &p.Prover, &p.Status); err != nil {
			slog.Error("ListConjectures scan failed", "error", err)
			continue
		}
		summaries = append(summaries, p)
	}
	return summaries
}

func (s *SQLiteStore) GetConjecture(id string) (data.Conjecture, bool) {
	var p data.Conjecture
	var hints, deps sql.NullString

	err := s.db.QueryRow(
		`SELECT id, title, difficulty, prover, status, preamble, lemma_statement, hints, skeleton, dependencies
		 FROM conjectures WHERE id = ?`, id,
	).Scan(&p.ID, &p.Title, &p.Difficulty, &p.Prover, &p.Status,
		&p.Preamble, &p.LemmaStatement, &hints, &p.Skeleton, &deps)

	if err == sql.ErrNoRows {
		return data.Conjecture{}, false
	}
	if err != nil {
		slog.Error("GetConjecture query failed", "error", err, "id", id)
		return data.Conjecture{}, false
	}

	if hints.Valid {
		json.Unmarshal([]byte(hints.String), &p.Hints)
	}
	if deps.Valid {
		p.Dependencies = json.RawMessage(deps.String)
	}

	return p, true
}

func (s *SQLiteStore) AddConjectures(conjectures []data.Conjecture) []string {
	var added []string
	for _, p := range conjectures {
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
			`INSERT INTO conjectures (id, title, difficulty, prover, status, preamble, lemma_statement, hints, skeleton, dependencies)
			 VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
			 ON CONFLICT (id) DO NOTHING`,
			p.ID, p.Title, p.Difficulty, p.Prover, p.Status,
			p.Preamble, p.LemmaStatement, string(hintsJSON), p.Skeleton, depsJSON,
		)
		if err != nil {
			slog.Error("AddConjectures insert failed", "error", err, "id", p.ID)
			continue
		}

		rows, _ := res.RowsAffected()
		if rows > 0 {
			added = append(added, p.ID)
		}
	}
	return added
}

func (s *SQLiteStore) AddCertificate(r data.Certificate) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddCertificate begin tx failed", "error", err)
		return
	}
	defer tx.Rollback()

	successInt := 0
	if r.Success {
		successInt = 1
	}

	_, err = tx.Exec(
		`INSERT INTO certificates (conjecture_id, username, success, proof_script, cost_usd, attempts, error_output)
		 VALUES (?, ?, ?, ?, ?, ?, ?)`,
		r.ConjectureID, r.Username, successInt, r.ProofScript, r.CostUSD, r.Attempts, r.ErrorOutput,
	)
	if err != nil {
		slog.Error("AddCertificate insert failed", "error", err)
		return
	}

	if r.Success {
		_, err = tx.Exec(`UPDATE conjectures SET status = 'proved' WHERE id = ?`, r.ConjectureID)
		if err != nil {
			slog.Error("AddCertificate update status failed", "error", err)
			return
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddCertificate commit failed", "error", err)
	}
}

func (s *SQLiteStore) AddContribution(cs data.ContributionSummary) {
	conjectureIDsJSON, _ := json.Marshal(cs.ConjectureIDs)
	reviewedByJSON, _ := json.Marshal(cs.ReviewedBy)
	var nftJSON *string
	if cs.NFTMetadata != nil {
		b, _ := json.Marshal(cs.NFTMetadata)
		n := string(b)
		nftJSON = &n
	}

	_, err := s.db.Exec(
		`INSERT INTO contributions (contribution_id, username, conjectures_attempted, conjectures_proved, total_cost_usd,
		 archive_sha256, nft_metadata, prover, conjecture_ids, archive_path, proof_status, reviewed_by)
		 VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
		 ON CONFLICT (contribution_id) DO UPDATE SET
		   conjectures_attempted = excluded.conjectures_attempted,
		   conjectures_proved = excluded.conjectures_proved,
		   total_cost_usd = excluded.total_cost_usd,
		   archive_sha256 = excluded.archive_sha256,
		   nft_metadata = excluded.nft_metadata,
		   prover = excluded.prover,
		   conjecture_ids = excluded.conjecture_ids,
		   archive_path = excluded.archive_path,
		   proof_status = excluded.proof_status,
		   reviewed_by = excluded.reviewed_by`,
		cs.ContributionID, cs.Username, cs.ConjecturesAttempted, cs.ConjecturesProved,
		cs.TotalCostUSD, cs.ArchiveSHA256, nftJSON, cs.Prover,
		string(conjectureIDsJSON), cs.ArchivePath, cs.ProofStatus, string(reviewedByJSON),
	)
	if err != nil {
		slog.Error("AddContribution insert failed", "error", err)
	}
}

func (s *SQLiteStore) ListReviewPackages() []data.ReviewPackageInfo {
	rows, err := s.db.Query(
		`SELECT contribution_id, username, prover, conjecture_ids, archive_sha256, proof_status, reviewed_by
		 FROM contributions ORDER BY created_at`)
	if err != nil {
		slog.Error("ListReviewPackages query failed", "error", err)
		return nil
	}
	defer rows.Close()

	var packages []data.ReviewPackageInfo
	for rows.Next() {
		var contributionID, username, prover, archiveSHA256, proofStatus string
		var conjectureIDsStr, reviewedByStr string

		if err := rows.Scan(&contributionID, &username, &prover, &conjectureIDsStr, &archiveSHA256, &proofStatus, &reviewedByStr); err != nil {
			slog.Error("ListReviewPackages scan failed", "error", err)
			continue
		}

		var conjectureIDs []string
		var reviewedBy []string
		json.Unmarshal([]byte(conjectureIDsStr), &conjectureIDs)
		json.Unmarshal([]byte(reviewedByStr), &reviewedBy)

		if len(conjectureIDs) == 0 {
			// Fallback: scan results for this user
			resultRows, err := s.db.Query(
				`SELECT DISTINCT conjecture_id FROM certificates WHERE username = ? AND success = 1`, username)
			if err == nil {
				for resultRows.Next() {
					var pid string
					if resultRows.Scan(&pid) == nil {
						conjectureIDs = append(conjectureIDs, pid)
					}
				}
				resultRows.Close()
			}
		}

		if prover == "" {
			prover = "rocq"
		}

		packages = append(packages, data.ReviewPackageInfo{
			ProverContributionID: contributionID,
			ProverUsername:       username,
			Prover:               prover,
			ConjectureIDs:        conjectureIDs,
			ArchiveURL:           fmt.Sprintf("/review-packages/%s/archive", contributionID),
			ArchiveSHA256:        archiveSHA256,
			ProofStatus:          proofStatus,
			ReviewedBy:           reviewedBy,
		})
	}
	return packages
}

func (s *SQLiteStore) GetArchivePath(contributionID string) (string, bool) {
	var path string
	err := s.db.QueryRow(`SELECT archive_path FROM contributions WHERE contribution_id = ?`, contributionID).Scan(&path)
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
		`INSERT INTO reviews (review_id, reviewer_username, packages_reviewed, conjectures_compared, package_rankings, recommendation, archive_sha256, nft_metadata)
		 VALUES (?, ?, ?, ?, ?, ?, ?, ?)`,
		r.ReviewID, r.ReviewerUsername, r.PackagesReviewed, r.ConjecturesCompared,
		string(rankingsJSON), r.Recommendation, r.ArchiveSHA256, nftJSON,
	)
	if err != nil {
		slog.Error("AddReview insert failed", "error", err)
		return
	}

	// Update reviewed_by for each contribution referenced in the review
	for _, pr := range r.PackageRankings {
		// Read current reviewed_by, add reviewer, write back
		var currentJSON string
		err := tx.QueryRow(`SELECT reviewed_by FROM contributions WHERE contribution_id = ?`, pr.ProverContributionID).Scan(&currentJSON)
		if err != nil {
			slog.Error("AddReview read reviewed_by failed", "error", err, "contribution_id", pr.ProverContributionID)
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
			_, err = tx.Exec(`UPDATE contributions SET reviewed_by = ? WHERE contribution_id = ?`,
				string(updatedJSON), pr.ProverContributionID)
			if err != nil {
				slog.Error("AddReview update reviewed_by failed", "error", err, "contribution_id", pr.ProverContributionID)
			}
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddReview commit failed", "error", err)
	}
}

// LoadConjectures loads conjecture JSON files from a directory into the database.
func (s *SQLiteStore) LoadConjectures(dir string) error {
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

		s.AddConjectures([]data.Conjecture{p})
	}
	return nil
}

// LoadSeedContributions loads seed contribution JSON files from a directory.
func (s *SQLiteStore) LoadSeedContributions(dir string) error {
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

		if cs.ArchivePath != "" && !filepath.IsAbs(cs.ArchivePath) {
			cs.ArchivePath = filepath.Join(dir, cs.ArchivePath)
		}

		s.AddContribution(cs)
	}
	return nil
}
