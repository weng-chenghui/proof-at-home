package data

// "prover" = machine/software (proof assistant, e.g. rocq/lean4);
// "contributor" = the human person who submitted or ran the proof.

import "encoding/json"

// Conjecture.Prover refers to the proof assistant software (e.g. "rocq", "lean4"), not the human.
type Conjecture struct {
	ID             string          `json:"id"`
	Title          string          `json:"title"`
	Difficulty     string          `json:"difficulty"`
	Prover         string          `json:"prover"`
	Status         string          `json:"status"`
	Preamble       string          `json:"preamble"`
	LemmaStatement string          `json:"lemma_statement"`
	Hints          []string        `json:"hints"`
	Skeleton       string          `json:"skeleton"`
	Dependencies   json.RawMessage `json:"dependencies,omitempty"`
}

type ConjectureSummary struct {
	ID         string `json:"id"`
	Title      string `json:"title"`
	Difficulty string `json:"difficulty"`
	Prover     string `json:"prover"`
	Status     string `json:"status"`
}

type ContributionResult struct {
	ContributionID string  `json:"contribution_id,omitempty"`
	ConjectureID   string  `json:"conjecture_id"`
	Username       string  `json:"username"`
	Success        bool    `json:"success"`
	ProofScript    string  `json:"proof_script"`
	CostUSD        float64 `json:"cost_usd"`
	Attempts       int     `json:"attempts"`
	ErrorOutput    string  `json:"error_output"`
}

type ContributionSummary struct {
	Username             string      `json:"username"`
	ContributionID       string      `json:"contribution_id"`
	ConjecturesAttempted int         `json:"conjectures_attempted"`
	ConjecturesProved    int         `json:"conjectures_proved"`
	TotalCostUSD         float64     `json:"total_cost_usd"`
	ArchiveSHA256        string      `json:"archive_sha256"`
	NFTMetadata          interface{} `json:"nft_metadata"`
	Prover               string      `json:"prover,omitempty"`
	ConjectureIDs        []string    `json:"conjecture_ids,omitempty"`
	ArchivePath          string      `json:"archive_path,omitempty"`
	ProofStatus          string      `json:"proof_status,omitempty"`
	CertifiedBy          []string    `json:"certified_by,omitempty"`
}

// ── Certificate types ──

type CertificatePackageInfo struct {
	ContributorContributionID string   `json:"contributor_contribution_id"`
	ContributorUsername       string   `json:"contributor_username"`
	Prover                    string   `json:"prover"` // proof assistant software, not the human
	ConjectureIDs             []string `json:"conjecture_ids"`
	ArchiveURL                string   `json:"archive_url"`
	ArchiveSHA256             string   `json:"archive_sha256"`
	ProofStatus               string   `json:"proof_status,omitempty"`
	CertifiedBy               []string `json:"certified_by,omitempty"`
}

type CertificateSummary struct {
	CertifierUsername   string                  `json:"certifier_username"`
	CertificateID       string                  `json:"certificate_id"`
	PackagesCertified   int                     `json:"packages_certified"`
	ConjecturesCompared int                     `json:"conjectures_compared"`
	PackageRankings     []PackageRankingSummary `json:"package_rankings"`
	Recommendation      string                  `json:"recommendation"`
	ArchiveSHA256       string                  `json:"archive_sha256"`
	NFTMetadata         interface{}             `json:"nft_metadata"`
}

type PackageRankingSummary struct {
	ContributorContributionID string  `json:"contributor_contribution_id"`
	Rank                      int     `json:"rank"`
	OverallScore              float64 `json:"overall_score"`
}
