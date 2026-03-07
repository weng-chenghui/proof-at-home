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

type Proof struct {
	ContributionID string  `json:"contribution_id,omitempty"`
	ConjectureID   string  `json:"conjecture_id"`
	Username       string  `json:"username"`
	Success        bool    `json:"success"`
	ProofScript    string  `json:"proof_script"`
	CostUSD        float64 `json:"cost_usd"`
	Attempts       int     `json:"attempts"`
	ErrorOutput    string  `json:"error_output"`
}

type Contribution struct {
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

// ── Command types ──

type Strategy struct {
	Name        string `json:"name"`
	Kind        string `json:"kind"`
	Prover      string `json:"prover"`
	Description string `json:"description"`
	Priority    int    `json:"priority"`
	Body        string `json:"body"`
}

// ── Certificate types ──

type ContributionReview struct {
	ContributorContributionID string   `json:"contributor_contribution_id"`
	ContributorUsername       string   `json:"contributor_username"`
	Prover                    string   `json:"prover"` // proof assistant software, not the human
	ConjectureIDs             []string `json:"conjecture_ids"`
	ArchiveURL                string   `json:"archive_url"`
	ArchiveSHA256             string   `json:"archive_sha256"`
	ProofStatus               string   `json:"proof_status,omitempty"`
	CertifiedBy               []string `json:"certified_by,omitempty"`
}

type Certificate struct {
	CertifierUsername   string                `json:"certifier_username"`
	CertificateID       string                `json:"certificate_id"`
	PackagesCertified   int                   `json:"packages_certified"`
	ConjecturesCompared int                   `json:"conjectures_compared"`
	PackageRankings     []ContributionRanking `json:"package_rankings"`
	Recommendation      string                `json:"recommendation"`
	ArchiveSHA256       string                `json:"archive_sha256"`
	NFTMetadata         interface{}           `json:"nft_metadata"`
}

type ContributionRanking struct {
	ContributorContributionID string  `json:"contributor_contribution_id"`
	Rank                      int     `json:"rank"`
	OverallScore              float64 `json:"overall_score"`
}

// ── Lesson types ──

type AIAnnotation struct {
	Zone        string   `json:"zone" yaml:"zone"`
	Context     string   `json:"context" yaml:"context"`
	Suggestions []string `json:"suggestions" yaml:"suggestions"`
}

type Lesson struct {
	LessonID       string         `json:"lesson_id" yaml:"lesson_id"`
	AuthorUsername string         `json:"author_username" yaml:"author_username"`
	Title          string         `json:"title" yaml:"title"`
	Topic          string         `json:"topic,omitempty" yaml:"topic,omitempty"`
	Difficulty     string         `json:"difficulty,omitempty" yaml:"difficulty,omitempty"`
	Description    string         `json:"description,omitempty" yaml:"description,omitempty"`
	Prerequisites  string         `json:"prerequisites,omitempty" yaml:"prerequisites,omitempty"`
	ConjectureIDs  []string       `json:"conjecture_ids" yaml:"conjecture_ids"`
	Published      bool           `json:"published" yaml:"published"`
	CreatedAt      string         `json:"created_at,omitempty" yaml:"-"`
	Content        string         `json:"content,omitempty" yaml:"-"`
	AIAnnotations  []AIAnnotation `json:"ai_annotations,omitempty" yaml:"ai_annotations,omitempty"`
}

// ── Series types ──

type Series struct {
	SeriesID       string   `json:"series_id" yaml:"series_id"`
	Title          string   `json:"title" yaml:"title"`
	AuthorUsername string   `json:"author_username" yaml:"author_username"`
	Difficulty     string   `json:"difficulty,omitempty" yaml:"difficulty,omitempty"`
	Description    string   `json:"description,omitempty" yaml:"description,omitempty"`
	LessonIDs      []string `json:"lesson_ids" yaml:"lesson_ids"`
	Published      bool     `json:"published" yaml:"published"`
	CreatedAt      string   `json:"created_at,omitempty" yaml:"-"`
	Content        string   `json:"content,omitempty" yaml:"-"`
}

// ── Exposition types ──

type Exposition struct {
	ExpositionID   string      `json:"exposition_id"`
	AuthorUsername string      `json:"author_username"`
	ContributionID string      `json:"contribution_id,omitempty"`
	ConjectureID   string      `json:"conjecture_id,omitempty"`
	Prover         string      `json:"prover,omitempty"`
	ProofScript    string      `json:"proof_script"`
	ExpositionText string      `json:"exposition_text"`
	CostUSD        float64     `json:"cost_usd"`
	StrategyUsed   string      `json:"strategy_used,omitempty"`
	NFTMetadata    interface{} `json:"nft_metadata"`
	Domain         string      `json:"domain,omitempty"`
	Title          string      `json:"title,omitempty"`
	Summary        string      `json:"summary,omitempty"`
}
