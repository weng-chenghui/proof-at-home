CREATE TABLE IF NOT EXISTS problems (
    id             TEXT PRIMARY KEY,
    title          TEXT NOT NULL DEFAULT '',
    difficulty     TEXT NOT NULL DEFAULT '',
    proof_assistant TEXT NOT NULL DEFAULT '',
    status         TEXT NOT NULL DEFAULT 'open',
    preamble       TEXT NOT NULL DEFAULT '',
    lemma_statement TEXT NOT NULL DEFAULT '',
    hints          JSONB NOT NULL DEFAULT '[]',
    skeleton       TEXT NOT NULL DEFAULT '',
    dependencies   JSONB
);

CREATE TABLE IF NOT EXISTS proof_results (
    id           SERIAL PRIMARY KEY,
    problem_id   TEXT NOT NULL,
    username     TEXT NOT NULL,
    success      BOOLEAN NOT NULL DEFAULT FALSE,
    proof_script TEXT NOT NULL DEFAULT '',
    cost_usd     DOUBLE PRECISION NOT NULL DEFAULT 0,
    attempts     INTEGER NOT NULL DEFAULT 0,
    error_output TEXT NOT NULL DEFAULT '',
    created_at   TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE INDEX IF NOT EXISTS idx_proof_results_problem_id ON proof_results(problem_id);
CREATE INDEX IF NOT EXISTS idx_proof_results_username ON proof_results(username);

CREATE TABLE IF NOT EXISTS sessions (
    session_id         TEXT PRIMARY KEY,
    username           TEXT NOT NULL,
    problems_attempted INTEGER NOT NULL DEFAULT 0,
    problems_proved    INTEGER NOT NULL DEFAULT 0,
    total_cost_usd     DOUBLE PRECISION NOT NULL DEFAULT 0,
    archive_sha256     TEXT NOT NULL DEFAULT '',
    nft_metadata       JSONB,
    proof_assistant    TEXT NOT NULL DEFAULT '',
    problem_ids        JSONB NOT NULL DEFAULT '[]',
    archive_path       TEXT NOT NULL DEFAULT '',
    proof_status       TEXT NOT NULL DEFAULT '',
    reviewed_by        JSONB NOT NULL DEFAULT '[]',
    created_at         TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS reviews (
    review_id          TEXT PRIMARY KEY,
    reviewer_username  TEXT NOT NULL,
    packages_reviewed  INTEGER NOT NULL DEFAULT 0,
    problems_compared  INTEGER NOT NULL DEFAULT 0,
    package_rankings   JSONB NOT NULL DEFAULT '[]',
    recommendation     TEXT NOT NULL DEFAULT '',
    archive_sha256     TEXT NOT NULL DEFAULT '',
    nft_metadata       JSONB,
    created_at         TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
