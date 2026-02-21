package data

import "encoding/json"

type Problem struct {
	ID             string          `json:"id"`
	Title          string          `json:"title"`
	Difficulty     string          `json:"difficulty"`
	ProofAssistant string          `json:"proof_assistant"`
	Status         string          `json:"status"`
	Preamble       string          `json:"preamble"`
	LemmaStatement string          `json:"lemma_statement"`
	Hints          []string        `json:"hints"`
	Skeleton       string          `json:"skeleton"`
	Dependencies   json.RawMessage `json:"dependencies,omitempty"`
}

type ProblemSummary struct {
	ID             string `json:"id"`
	Title          string `json:"title"`
	Difficulty     string `json:"difficulty"`
	ProofAssistant string `json:"proof_assistant"`
	Status         string `json:"status"`
}

type ProofResult struct {
	ProblemID   string  `json:"problem_id"`
	Username    string  `json:"username"`
	Success     bool    `json:"success"`
	ProofScript string  `json:"proof_script"`
	CostUSD     float64 `json:"cost_usd"`
	Attempts    int     `json:"attempts"`
	ErrorOutput string  `json:"error_output"`
}

type SessionSummary struct {
	Username          string      `json:"username"`
	SessionID         string      `json:"session_id"`
	ProblemsAttempted int         `json:"problems_attempted"`
	ProblemsProved    int         `json:"problems_proved"`
	TotalCostUSD      float64     `json:"total_cost_usd"`
	ArchiveSHA256     string      `json:"archive_sha256"`
	NFTMetadata       interface{} `json:"nft_metadata"`
	ProofAssistant    string      `json:"proof_assistant,omitempty"`
	ProblemIDs        []string    `json:"problem_ids,omitempty"`
	ArchivePath       string      `json:"archive_path,omitempty"`
}

// ── Review types ──

type ReviewPackageInfo struct {
	ProverSessionID string   `json:"prover_session_id"`
	ProverUsername  string   `json:"prover_username"`
	ProofAssistant string   `json:"proof_assistant"`
	ProblemIDs     []string `json:"problem_ids"`
	ArchiveURL     string   `json:"archive_url"`
	ArchiveSHA256  string   `json:"archive_sha256"`
}

type ReviewSummary struct {
	ReviewerUsername string                  `json:"reviewer_username"`
	ReviewID         string                 `json:"review_id"`
	PackagesReviewed int                    `json:"packages_reviewed"`
	ProblemsCompared int                    `json:"problems_compared"`
	PackageRankings  []PackageRankingSummary `json:"package_rankings"`
	Recommendation   string                 `json:"recommendation"`
	ArchiveSHA256    string                 `json:"archive_sha256"`
	NFTMetadata      interface{}            `json:"nft_metadata"`
}

type PackageRankingSummary struct {
	ProverSessionID string  `json:"prover_session_id"`
	Rank            int     `json:"rank"`
	OverallScore    float64 `json:"overall_score"`
}
