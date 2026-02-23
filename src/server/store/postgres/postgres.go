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

func (s *PostgresStore) ListConjectures() []data.ConjectureSummary {
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

func (s *PostgresStore) GetConjecture(id string) (data.Conjecture, bool) {
	var p data.Conjecture
	var hints, deps []byte

	err := s.db.QueryRow(
		`SELECT id, title, difficulty, prover, status, preamble, lemma_statement, hints, skeleton, dependencies
		 FROM conjectures WHERE id = $1`, id,
	).Scan(&p.ID, &p.Title, &p.Difficulty, &p.Prover, &p.Status,
		&p.Preamble, &p.LemmaStatement, &hints, &p.Skeleton, &deps)

	if err == sql.ErrNoRows {
		return data.Conjecture{}, false
	}
	if err != nil {
		slog.Error("GetConjecture query failed", "error", err, "id", id)
		return data.Conjecture{}, false
	}

	if hints != nil {
		json.Unmarshal(hints, &p.Hints)
	}
	if deps != nil {
		p.Dependencies = json.RawMessage(deps)
	}

	return p, true
}

func (s *PostgresStore) AddConjectures(conjectures []data.Conjecture) []string {
	var added []string
	for _, p := range conjectures {
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
			`INSERT INTO conjectures (id, title, difficulty, prover, status, preamble, lemma_statement, hints, skeleton, dependencies)
			 VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
			 ON CONFLICT (id) DO NOTHING`,
			p.ID, p.Title, p.Difficulty, p.Prover, p.Status,
			p.Preamble, p.LemmaStatement, hintsJSON, p.Skeleton, depsJSON,
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

func (s *PostgresStore) AddContributionResult(r data.ContributionResult) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddContributionResult begin tx failed", "error", err)
		return
	}
	defer tx.Rollback()

	_, err = tx.Exec(
		`INSERT INTO contribution_results (conjecture_id, username, success, proof_script, cost_usd, attempts, error_output)
		 VALUES ($1, $2, $3, $4, $5, $6, $7)`,
		r.ConjectureID, r.Username, r.Success, r.ProofScript, r.CostUSD, r.Attempts, r.ErrorOutput,
	)
	if err != nil {
		slog.Error("AddContributionResult insert failed", "error", err)
		return
	}

	if r.Success {
		_, err = tx.Exec(`UPDATE conjectures SET status = 'proved' WHERE id = $1`, r.ConjectureID)
		if err != nil {
			slog.Error("AddContributionResult update status failed", "error", err)
			return
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddContributionResult commit failed", "error", err)
	}
}

func (s *PostgresStore) AddContribution(cs data.ContributionSummary) {
	conjectureIDsJSON, _ := json.Marshal(cs.ConjectureIDs)
	certifiedByJSON, _ := json.Marshal(cs.CertifiedBy)
	var nftJSON []byte
	if cs.NFTMetadata != nil {
		nftJSON, _ = json.Marshal(cs.NFTMetadata)
	}

	_, err := s.db.Exec(
		`INSERT INTO contributions (contribution_id, username, conjectures_attempted, conjectures_proved, total_cost_usd,
		 archive_sha256, nft_metadata, prover, conjecture_ids, archive_path, proof_status, certified_by)
		 VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12)
		 ON CONFLICT (contribution_id) DO UPDATE SET
		   conjectures_attempted = EXCLUDED.conjectures_attempted,
		   conjectures_proved = EXCLUDED.conjectures_proved,
		   total_cost_usd = EXCLUDED.total_cost_usd,
		   archive_sha256 = EXCLUDED.archive_sha256,
		   nft_metadata = EXCLUDED.nft_metadata,
		   prover = EXCLUDED.prover,
		   conjecture_ids = EXCLUDED.conjecture_ids,
		   archive_path = EXCLUDED.archive_path,
		   proof_status = EXCLUDED.proof_status,
		   certified_by = EXCLUDED.certified_by`,
		cs.ContributionID, cs.Username, cs.ConjecturesAttempted, cs.ConjecturesProved,
		cs.TotalCostUSD, cs.ArchiveSHA256, nftJSON, cs.Prover,
		conjectureIDsJSON, cs.ArchivePath, cs.ProofStatus, certifiedByJSON,
	)
	if err != nil {
		slog.Error("AddContribution insert failed", "error", err)
	}
}

func (s *PostgresStore) ListCertificatePackages() []data.CertificatePackageInfo {
	rows, err := s.db.Query(
		`SELECT contribution_id, username, prover, conjecture_ids, archive_sha256, proof_status, certified_by
		 FROM contributions ORDER BY created_at`)
	if err != nil {
		slog.Error("ListCertificatePackages query failed", "error", err)
		return nil
	}
	defer rows.Close()

	var packages []data.CertificatePackageInfo
	for rows.Next() {
		var contributionID, username, prover, archiveSHA256, proofStatus string
		var conjectureIDsJSON, certifiedByJSON []byte

		if err := rows.Scan(&contributionID, &username, &prover, &conjectureIDsJSON, &archiveSHA256, &proofStatus, &certifiedByJSON); err != nil {
			slog.Error("ListCertificatePackages scan failed", "error", err)
			continue
		}

		var conjectureIDs []string
		var certifiedBy []string
		json.Unmarshal(conjectureIDsJSON, &conjectureIDs)
		json.Unmarshal(certifiedByJSON, &certifiedBy)

		if len(conjectureIDs) == 0 {
			// Fallback: scan results for this user
			resultRows, err := s.db.Query(
				`SELECT DISTINCT conjecture_id FROM contribution_results WHERE username = $1 AND success = true`, username)
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

		packages = append(packages, data.CertificatePackageInfo{
			ProverContributionID: contributionID,
			ProverUsername:       username,
			Prover:               prover,
			ConjectureIDs:        conjectureIDs,
			ArchiveURL:           fmt.Sprintf("/certificate-packages/%s/archive", contributionID),
			ArchiveSHA256:        archiveSHA256,
			ProofStatus:          proofStatus,
			CertifiedBy:          certifiedBy,
		})
	}
	return packages
}

func (s *PostgresStore) GetArchivePath(contributionID string) (string, bool) {
	var path string
	err := s.db.QueryRow(`SELECT archive_path FROM contributions WHERE contribution_id = $1`, contributionID).Scan(&path)
	if err != nil {
		return "", false
	}
	return path, true
}

func (s *PostgresStore) AddCertificate(r data.CertificateSummary) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddCertificate begin tx failed", "error", err)
		return
	}
	defer tx.Rollback()

	rankingsJSON, _ := json.Marshal(r.PackageRankings)
	var nftJSON []byte
	if r.NFTMetadata != nil {
		nftJSON, _ = json.Marshal(r.NFTMetadata)
	}

	_, err = tx.Exec(
		`INSERT INTO certificates (certificate_id, certifier_username, packages_certified, conjectures_compared, package_rankings, recommendation, archive_sha256, nft_metadata)
		 VALUES ($1, $2, $3, $4, $5, $6, $7, $8)`,
		r.CertificateID, r.CertifierUsername, r.PackagesCertified, r.ConjecturesCompared,
		rankingsJSON, r.Recommendation, r.ArchiveSHA256, nftJSON,
	)
	if err != nil {
		slog.Error("AddCertificate insert failed", "error", err)
		return
	}

	// Update certified_by for each contribution referenced in the certificate
	for _, pr := range r.PackageRankings {
		_, err = tx.Exec(
			`UPDATE contributions SET certified_by = (
				SELECT jsonb_agg(DISTINCT val)
				FROM (
					SELECT jsonb_array_elements_text(certified_by) AS val
					UNION
					SELECT $1
				) sub
			) WHERE contribution_id = $2`,
			r.CertifierUsername, pr.ProverContributionID,
		)
		if err != nil {
			slog.Error("AddCertificate update certified_by failed", "error", err, "contribution_id", pr.ProverContributionID)
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddCertificate commit failed", "error", err)
	}
}

// LoadConjectures loads conjecture JSON files from a directory into the database.
func (s *PostgresStore) LoadConjectures(dir string) error {
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
func (s *PostgresStore) LoadSeedContributions(dir string) error {
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
