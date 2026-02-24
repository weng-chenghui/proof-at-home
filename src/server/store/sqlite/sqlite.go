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

func (s *SQLiteStore) AddContributionResult(r data.ContributionResult) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddContributionResult begin tx failed", "error", err)
		return
	}
	defer tx.Rollback()

	successInt := 0
	if r.Success {
		successInt = 1
	}

	_, err = tx.Exec(
		`INSERT INTO contribution_results (contribution_id, conjecture_id, username, success, proof_script, cost_usd, attempts, error_output)
		 VALUES (?, ?, ?, ?, ?, ?, ?, ?)`,
		r.ContributionID, r.ConjectureID, r.Username, successInt, r.ProofScript, r.CostUSD, r.Attempts, r.ErrorOutput,
	)
	if err != nil {
		slog.Error("AddContributionResult insert failed", "error", err)
		return
	}

	if r.Success {
		_, err = tx.Exec(`UPDATE conjectures SET status = 'proved' WHERE id = ?`, r.ConjectureID)
		if err != nil {
			slog.Error("AddContributionResult update status failed", "error", err)
			return
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddContributionResult commit failed", "error", err)
	}
}

func (s *SQLiteStore) AddContribution(cs data.ContributionSummary) {
	conjectureIDsJSON, _ := json.Marshal(cs.ConjectureIDs)
	certifiedByJSON, _ := json.Marshal(cs.CertifiedBy)
	var nftJSON *string
	if cs.NFTMetadata != nil {
		b, _ := json.Marshal(cs.NFTMetadata)
		n := string(b)
		nftJSON = &n
	}

	_, err := s.db.Exec(
		`INSERT INTO contributions (contribution_id, username, conjectures_attempted, conjectures_proved, total_cost_usd,
		 archive_sha256, nft_metadata, prover, conjecture_ids, archive_path, proof_status, certified_by)
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
		   certified_by = excluded.certified_by`,
		cs.ContributionID, cs.Username, cs.ConjecturesAttempted, cs.ConjecturesProved,
		cs.TotalCostUSD, cs.ArchiveSHA256, nftJSON, cs.Prover,
		string(conjectureIDsJSON), cs.ArchivePath, cs.ProofStatus, string(certifiedByJSON),
	)
	if err != nil {
		slog.Error("AddContribution insert failed", "error", err)
	}
}

func (s *SQLiteStore) GetContribution(id string) (data.ContributionSummary, bool) {
	var cs data.ContributionSummary
	var nftJSON, conjectureIDsStr, certifiedByStr sql.NullString
	err := s.db.QueryRow(
		`SELECT contribution_id, username, conjectures_attempted, conjectures_proved,
		 total_cost_usd, archive_sha256, nft_metadata, prover, conjecture_ids,
		 archive_path, proof_status, certified_by
		 FROM contributions WHERE contribution_id = ?`, id,
	).Scan(&cs.ContributionID, &cs.Username, &cs.ConjecturesAttempted, &cs.ConjecturesProved,
		&cs.TotalCostUSD, &cs.ArchiveSHA256, &nftJSON, &cs.Prover, &conjectureIDsStr,
		&cs.ArchivePath, &cs.ProofStatus, &certifiedByStr)

	if err == sql.ErrNoRows {
		return data.ContributionSummary{}, false
	}
	if err != nil {
		slog.Error("GetContribution query failed", "error", err, "id", id)
		return data.ContributionSummary{}, false
	}
	if nftJSON.Valid {
		json.Unmarshal([]byte(nftJSON.String), &cs.NFTMetadata)
	}
	if conjectureIDsStr.Valid {
		json.Unmarshal([]byte(conjectureIDsStr.String), &cs.ConjectureIDs)
	}
	if certifiedByStr.Valid {
		json.Unmarshal([]byte(certifiedByStr.String), &cs.CertifiedBy)
	}
	return cs, true
}

func (s *SQLiteStore) UpdateContribution(id string, cs data.ContributionSummary) {
	// Use UPSERT — set contribution_id to the path id, merge fields
	cs.ContributionID = id
	s.AddContribution(cs)
}

func (s *SQLiteStore) ListContributionResults(contributionID string) []data.ContributionResult {
	rows, err := s.db.Query(
		`SELECT contribution_id, conjecture_id, username, success, proof_script, cost_usd, attempts, error_output
		 FROM contribution_results WHERE contribution_id = ? ORDER BY id`, contributionID)
	if err != nil {
		slog.Error("ListContributionResults query failed", "error", err)
		return nil
	}
	defer rows.Close()

	var results []data.ContributionResult
	for rows.Next() {
		var r data.ContributionResult
		var success int
		if err := rows.Scan(&r.ContributionID, &r.ConjectureID, &r.Username, &success, &r.ProofScript, &r.CostUSD, &r.Attempts, &r.ErrorOutput); err != nil {
			slog.Error("ListContributionResults scan failed", "error", err)
			continue
		}
		r.Success = success != 0
		results = append(results, r)
	}
	return results
}

func (s *SQLiteStore) ListCertificatePackages() []data.CertificatePackageInfo {
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
		var conjectureIDsStr, certifiedByStr string

		if err := rows.Scan(&contributionID, &username, &prover, &conjectureIDsStr, &archiveSHA256, &proofStatus, &certifiedByStr); err != nil {
			slog.Error("ListCertificatePackages scan failed", "error", err)
			continue
		}

		var conjectureIDs []string
		var certifiedBy []string
		json.Unmarshal([]byte(conjectureIDsStr), &conjectureIDs)
		json.Unmarshal([]byte(certifiedByStr), &certifiedBy)

		if len(conjectureIDs) == 0 {
			// Fallback: scan results for this user
			resultRows, err := s.db.Query(
				`SELECT DISTINCT conjecture_id FROM contribution_results WHERE username = ? AND success = 1`, username)
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

func (s *SQLiteStore) GetArchivePath(contributionID string) (string, bool) {
	var path string
	err := s.db.QueryRow(`SELECT archive_path FROM contributions WHERE contribution_id = ?`, contributionID).Scan(&path)
	if err != nil {
		return "", false
	}
	return path, true
}

func (s *SQLiteStore) AddCertificate(r data.CertificateSummary) {
	tx, err := s.db.Begin()
	if err != nil {
		slog.Error("AddCertificate begin tx failed", "error", err)
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
		`INSERT INTO certificates (certificate_id, certifier_username, packages_certified, conjectures_compared, package_rankings, recommendation, archive_sha256, nft_metadata)
		 VALUES (?, ?, ?, ?, ?, ?, ?, ?)`,
		r.CertificateID, r.CertifierUsername, r.PackagesCertified, r.ConjecturesCompared,
		string(rankingsJSON), r.Recommendation, r.ArchiveSHA256, nftJSON,
	)
	if err != nil {
		slog.Error("AddCertificate insert failed", "error", err)
		return
	}

	// Update certified_by for each contribution referenced in the certificate
	for _, pr := range r.PackageRankings {
		// Read current certified_by, add certifier, write back
		var currentJSON string
		err := tx.QueryRow(`SELECT certified_by FROM contributions WHERE contribution_id = ?`, pr.ProverContributionID).Scan(&currentJSON)
		if err != nil {
			slog.Error("AddCertificate read certified_by failed", "error", err, "contribution_id", pr.ProverContributionID)
			continue
		}

		var current []string
		json.Unmarshal([]byte(currentJSON), &current)

		// Add certifier if not already present
		found := false
		for _, certifier := range current {
			if certifier == r.CertifierUsername {
				found = true
				break
			}
		}
		if !found {
			current = append(current, r.CertifierUsername)
			updatedJSON, _ := json.Marshal(current)
			_, err = tx.Exec(`UPDATE contributions SET certified_by = ? WHERE contribution_id = ?`,
				string(updatedJSON), pr.ProverContributionID)
			if err != nil {
				slog.Error("AddCertificate update certified_by failed", "error", err, "contribution_id", pr.ProverContributionID)
			}
		}
	}

	if err := tx.Commit(); err != nil {
		slog.Error("AddCertificate commit failed", "error", err)
	}
}

// ListContributions returns all contribution summaries.
func (s *SQLiteStore) ListContributions() []data.ContributionSummary {
	rows, err := s.db.Query(
		`SELECT contribution_id, username, conjectures_attempted, conjectures_proved,
		 total_cost_usd, archive_sha256, nft_metadata, prover, conjecture_ids,
		 archive_path, proof_status, certified_by
		 FROM contributions ORDER BY created_at`)
	if err != nil {
		slog.Error("ListContributions query failed", "error", err)
		return nil
	}
	defer rows.Close()

	var results []data.ContributionSummary
	for rows.Next() {
		var cs data.ContributionSummary
		var nftJSON, conjectureIDsStr, certifiedByStr sql.NullString
		if err := rows.Scan(&cs.ContributionID, &cs.Username, &cs.ConjecturesAttempted, &cs.ConjecturesProved,
			&cs.TotalCostUSD, &cs.ArchiveSHA256, &nftJSON, &cs.Prover, &conjectureIDsStr,
			&cs.ArchivePath, &cs.ProofStatus, &certifiedByStr); err != nil {
			slog.Error("ListContributions scan failed", "error", err)
			continue
		}
		if nftJSON.Valid {
			json.Unmarshal([]byte(nftJSON.String), &cs.NFTMetadata)
		}
		if conjectureIDsStr.Valid {
			json.Unmarshal([]byte(conjectureIDsStr.String), &cs.ConjectureIDs)
		}
		if certifiedByStr.Valid {
			json.Unmarshal([]byte(certifiedByStr.String), &cs.CertifiedBy)
		}
		results = append(results, cs)
	}
	return results
}

// ListCertificates returns all certificate summaries.
func (s *SQLiteStore) ListCertificates() []data.CertificateSummary {
	rows, err := s.db.Query(
		`SELECT certificate_id, certifier_username, packages_certified, conjectures_compared,
		 package_rankings, recommendation, archive_sha256, nft_metadata
		 FROM certificates ORDER BY created_at`)
	if err != nil {
		slog.Error("ListCertificates query failed", "error", err)
		return nil
	}
	defer rows.Close()

	var results []data.CertificateSummary
	for rows.Next() {
		var cs data.CertificateSummary
		var rankingsJSON, nftJSON sql.NullString
		if err := rows.Scan(&cs.CertificateID, &cs.CertifierUsername, &cs.PackagesCertified, &cs.ConjecturesCompared,
			&rankingsJSON, &cs.Recommendation, &cs.ArchiveSHA256, &nftJSON); err != nil {
			slog.Error("ListCertificates scan failed", "error", err)
			continue
		}
		if rankingsJSON.Valid {
			json.Unmarshal([]byte(rankingsJSON.String), &cs.PackageRankings)
		}
		if nftJSON.Valid {
			json.Unmarshal([]byte(nftJSON.String), &cs.NFTMetadata)
		}
		results = append(results, cs)
	}
	return results
}

// RebuildFromDir rebuilds the entire SQLite cache from the git data repo directory.
// It performs an atomic swap: DELETE all rows, then re-INSERT from the filesystem.
func (s *SQLiteStore) RebuildFromDir(repoPath string) error {
	tx, err := s.db.Begin()
	if err != nil {
		return fmt.Errorf("begin rebuild tx: %w", err)
	}
	defer tx.Rollback()

	// Clear all tables
	tables := []string{"contribution_results", "certificates", "contributions", "conjectures"}
	for _, table := range tables {
		if _, err := tx.Exec("DELETE FROM " + table); err != nil {
			return fmt.Errorf("clearing %s: %w", table, err)
		}
	}

	// Walk conjectures/
	conjecturesDir := filepath.Join(repoPath, "conjectures")
	if entries, err := os.ReadDir(conjecturesDir); err == nil {
		for _, entry := range entries {
			if entry.IsDir() || filepath.Ext(entry.Name()) != ".json" {
				continue
			}
			raw, err := os.ReadFile(filepath.Join(conjecturesDir, entry.Name()))
			if err != nil {
				slog.Error("RebuildFromDir: failed to read conjecture", "file", entry.Name(), "error", err)
				continue
			}
			var c data.Conjecture
			if err := json.Unmarshal(raw, &c); err != nil {
				slog.Error("RebuildFromDir: failed to parse conjecture", "file", entry.Name(), "error", err)
				continue
			}
			if c.ID == "" {
				continue
			}
			if c.Status == "" {
				c.Status = "open"
			}
			hintsJSON, _ := json.Marshal(c.Hints)
			var depsJSON *string
			if c.Dependencies != nil {
				d := string(c.Dependencies)
				depsJSON = &d
			}
			_, err = tx.Exec(
				`INSERT INTO conjectures (id, title, difficulty, prover, status, preamble, lemma_statement, hints, skeleton, dependencies)
				 VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
				 ON CONFLICT (id) DO NOTHING`,
				c.ID, c.Title, c.Difficulty, c.Prover, c.Status,
				c.Preamble, c.LemmaStatement, string(hintsJSON), c.Skeleton, depsJSON,
			)
			if err != nil {
				slog.Error("RebuildFromDir: failed to insert conjecture", "id", c.ID, "error", err)
			}
		}
	}

	// Walk contributions/*/summary.json + results/*.json
	contributionsDir := filepath.Join(repoPath, "contributions")
	if entries, err := os.ReadDir(contributionsDir); err == nil {
		for _, entry := range entries {
			if !entry.IsDir() {
				continue
			}
			contribID := entry.Name()
			contribDir := filepath.Join(contributionsDir, contribID)

			// Read summary.json
			summaryPath := filepath.Join(contribDir, "summary.json")
			if raw, err := os.ReadFile(summaryPath); err == nil {
				var cs data.ContributionSummary
				if err := json.Unmarshal(raw, &cs); err == nil {
					conjectureIDsJSON, _ := json.Marshal(cs.ConjectureIDs)
					certifiedByJSON, _ := json.Marshal(cs.CertifiedBy)
					var nftJSON *string
					if cs.NFTMetadata != nil {
						b, _ := json.Marshal(cs.NFTMetadata)
						n := string(b)
						nftJSON = &n
					}
					_, err = tx.Exec(
						`INSERT INTO contributions (contribution_id, username, conjectures_attempted, conjectures_proved, total_cost_usd,
						 archive_sha256, nft_metadata, prover, conjecture_ids, archive_path, proof_status, certified_by)
						 VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
						 ON CONFLICT (contribution_id) DO NOTHING`,
						cs.ContributionID, cs.Username, cs.ConjecturesAttempted, cs.ConjecturesProved,
						cs.TotalCostUSD, cs.ArchiveSHA256, nftJSON, cs.Prover,
						string(conjectureIDsJSON), cs.ArchivePath, cs.ProofStatus, string(certifiedByJSON),
					)
					if err != nil {
						slog.Error("RebuildFromDir: failed to insert contribution", "id", contribID, "error", err)
					}
				}
			}

			// Read results/*.json
			resultsDir := filepath.Join(contribDir, "results")
			if resultEntries, err := os.ReadDir(resultsDir); err == nil {
				for _, re := range resultEntries {
					if re.IsDir() || filepath.Ext(re.Name()) != ".json" {
						continue
					}
					raw, err := os.ReadFile(filepath.Join(resultsDir, re.Name()))
					if err != nil {
						continue
					}
					var r data.ContributionResult
					if err := json.Unmarshal(raw, &r); err != nil {
						continue
					}
					if r.ContributionID == "" {
						r.ContributionID = contribID
					}
					successInt := 0
					if r.Success {
						successInt = 1
					}
					_, err = tx.Exec(
						`INSERT INTO contribution_results (contribution_id, conjecture_id, username, success, proof_script, cost_usd, attempts, error_output)
						 VALUES (?, ?, ?, ?, ?, ?, ?, ?)`,
						r.ContributionID, r.ConjectureID, r.Username, successInt, r.ProofScript, r.CostUSD, r.Attempts, r.ErrorOutput,
					)
					if err != nil {
						slog.Error("RebuildFromDir: failed to insert result", "error", err)
					}

					// Update conjecture status if proved
					if r.Success {
						tx.Exec(`UPDATE conjectures SET status = 'proved' WHERE id = ?`, r.ConjectureID)
					}
				}
			}
		}
	}

	// Walk certificates/*/summary.json
	certificatesDir := filepath.Join(repoPath, "certificates")
	if entries, err := os.ReadDir(certificatesDir); err == nil {
		for _, entry := range entries {
			if !entry.IsDir() {
				continue
			}
			summaryPath := filepath.Join(certificatesDir, entry.Name(), "summary.json")
			raw, err := os.ReadFile(summaryPath)
			if err != nil {
				continue
			}
			var cs data.CertificateSummary
			if err := json.Unmarshal(raw, &cs); err != nil {
				continue
			}
			rankingsJSON, _ := json.Marshal(cs.PackageRankings)
			var nftJSON *string
			if cs.NFTMetadata != nil {
				b, _ := json.Marshal(cs.NFTMetadata)
				n := string(b)
				nftJSON = &n
			}
			_, err = tx.Exec(
				`INSERT INTO certificates (certificate_id, certifier_username, packages_certified, conjectures_compared, package_rankings, recommendation, archive_sha256, nft_metadata)
				 VALUES (?, ?, ?, ?, ?, ?, ?, ?)`,
				cs.CertificateID, cs.CertifierUsername, cs.PackagesCertified, cs.ConjecturesCompared,
				string(rankingsJSON), cs.Recommendation, cs.ArchiveSHA256, nftJSON,
			)
			if err != nil {
				slog.Error("RebuildFromDir: failed to insert certificate", "id", cs.CertificateID, "error", err)
			}

			// Update certified_by for contributions referenced in rankings
			for _, pr := range cs.PackageRankings {
				var currentJSON string
				err := tx.QueryRow(`SELECT certified_by FROM contributions WHERE contribution_id = ?`, pr.ProverContributionID).Scan(&currentJSON)
				if err != nil {
					continue
				}
				var current []string
				json.Unmarshal([]byte(currentJSON), &current)
				found := false
				for _, c := range current {
					if c == cs.CertifierUsername {
						found = true
						break
					}
				}
				if !found {
					current = append(current, cs.CertifierUsername)
					updatedJSON, _ := json.Marshal(current)
					tx.Exec(`UPDATE contributions SET certified_by = ? WHERE contribution_id = ?`,
						string(updatedJSON), pr.ProverContributionID)
				}
			}
		}
	}

	if err := tx.Commit(); err != nil {
		return fmt.Errorf("commit rebuild tx: %w", err)
	}

	slog.Info("RebuildFromDir complete", "path", repoPath)
	return nil
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
