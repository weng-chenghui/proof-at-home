package data

// "prover" = machine/software (proof assistant, e.g. rocq/lean4);
// "contributor" = the human person who submitted or ran the proof.

// Conjecture.Prover refers to the proof assistant software (e.g. "rocq", "lean4"), not the human.
type Conjecture struct {
	ID             string        `json:"id" toml:"id" yaml:"id"`
	Title          string        `json:"title" toml:"title" yaml:"title"`
	Difficulty     string        `json:"difficulty" toml:"difficulty" yaml:"difficulty"`
	Prover         string        `json:"prover" toml:"prover" yaml:"prover"`
	Status         string        `json:"status" toml:"status" yaml:"status"`
	Preamble       string        `json:"preamble" toml:"preamble" yaml:"preamble"`
	LemmaStatement string        `json:"lemma_statement" toml:"lemma_statement" yaml:"lemma_statement"`
	Hints          []string      `json:"hints" toml:"hints" yaml:"hints"`
	Skeleton       string        `json:"skeleton" toml:"skeleton" yaml:"skeleton"`
	Dependencies   *Dependencies `json:"dependencies,omitempty" toml:"dependencies,omitempty" yaml:"dependencies,omitempty"`
}

type Dependencies struct {
	LeanToolchain string   `json:"lean_toolchain,omitempty" toml:"lean_toolchain,omitempty" yaml:"lean_toolchain,omitempty"`
	LakePackages  []string `json:"lake_packages,omitempty" toml:"lake_packages,omitempty" yaml:"lake_packages,omitempty"`
	RocqVersion   string   `json:"rocq_version,omitempty" toml:"rocq_version,omitempty" yaml:"rocq_version,omitempty"`
	OpamPackages  []string `json:"opam_packages,omitempty" toml:"opam_packages,omitempty" yaml:"opam_packages,omitempty"`
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

// ── Reference types (CSL-JSON compatible subset) ──

// CslName represents an author/editor name per CSL-JSON spec.
type CslName struct {
	Family  string `json:"family,omitempty" yaml:"family,omitempty"`
	Given   string `json:"given,omitempty" yaml:"given,omitempty"`
	Literal string `json:"literal,omitempty" yaml:"literal,omitempty"` // for organizations
}

// CslDate represents a date per CSL-JSON spec.
type CslDate struct {
	DateParts [][]int `json:"date-parts,omitempty" yaml:"date-parts,omitempty"` // e.g. [[2020, 3, 15]]
	Literal   string  `json:"literal,omitempty" yaml:"literal,omitempty"`
}

// Reference is a CSL-JSON compatible bibliographic item.
// We store the core fields needed for lesson citations; the full CSL-JSON
// spec has ~60 fields but these cover 95%+ of our use cases.
type Reference struct {
	ID             string    `json:"id,omitempty" yaml:"id,omitempty"`
	Type           string    `json:"type,omitempty" yaml:"type,omitempty"` // article-journal, book, chapter, webpage, paper-conference, thesis, report
	Title          string    `json:"title" yaml:"title"`
	Author         []CslName `json:"author,omitempty" yaml:"author,omitempty"`
	Issued         *CslDate  `json:"issued,omitempty" yaml:"issued,omitempty"`
	ContainerTitle string    `json:"container-title,omitempty" yaml:"container-title,omitempty"` // journal or book name
	Volume         string    `json:"volume,omitempty" yaml:"volume,omitempty"`
	Issue          string    `json:"issue,omitempty" yaml:"issue,omitempty"`
	Page           string    `json:"page,omitempty" yaml:"page,omitempty"`
	DOI            string    `json:"DOI,omitempty" yaml:"DOI,omitempty"`
	URL            string    `json:"URL,omitempty" yaml:"URL,omitempty"`
	ISBN           string    `json:"ISBN,omitempty" yaml:"ISBN,omitempty"`
	Publisher      string    `json:"publisher,omitempty" yaml:"publisher,omitempty"`
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
	References     []Reference    `json:"references,omitempty" yaml:"references,omitempty"`
}

// ── Note types ──

type Note struct {
	NoteID         string `json:"note_id" toml:"note_id"`
	LessonID       string `json:"lesson_id" toml:"lesson_id"`
	ContentHash    string `json:"content_hash" toml:"content_hash"`
	AnchorText     string `json:"anchor_text" toml:"anchor_text"`
	LineStart      int    `json:"line_start" toml:"line_start"`
	LineEnd        int    `json:"line_end" toml:"line_end"`
	Content        string `json:"content" toml:"content"`
	HighlightColor string `json:"highlight_color" toml:"highlight_color"`
	UserID         string `json:"user_id" toml:"user_id"`
	Username       string `json:"username" toml:"username"`
	Status         string `json:"status" toml:"status"`
	CreatedAt      string `json:"created_at" toml:"created_at"`
	UpdatedAt      string `json:"updated_at" toml:"updated_at"`
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
