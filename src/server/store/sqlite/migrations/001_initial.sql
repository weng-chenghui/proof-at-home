CREATE TABLE IF NOT EXISTS conjectures (
    id              TEXT PRIMARY KEY,
    title           TEXT NOT NULL DEFAULT '',
    difficulty      TEXT NOT NULL DEFAULT '',
    prover          TEXT NOT NULL DEFAULT '',
    status          TEXT NOT NULL DEFAULT 'open',
    preamble        TEXT NOT NULL DEFAULT '',
    lemma_statement TEXT NOT NULL DEFAULT '',
    hints           TEXT NOT NULL DEFAULT '[]',
    skeleton        TEXT NOT NULL DEFAULT '',
    dependencies    TEXT
);

CREATE TABLE IF NOT EXISTS certificates (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    conjecture_id TEXT NOT NULL,
    username     TEXT NOT NULL,
    success      INTEGER NOT NULL DEFAULT 0,
    proof_script TEXT NOT NULL DEFAULT '',
    cost_usd     REAL NOT NULL DEFAULT 0,
    attempts     INTEGER NOT NULL DEFAULT 0,
    error_output TEXT NOT NULL DEFAULT '',
    created_at   TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX IF NOT EXISTS idx_certificates_conjecture_id ON certificates(conjecture_id);
CREATE INDEX IF NOT EXISTS idx_certificates_username ON certificates(username);

CREATE TABLE IF NOT EXISTS contributions (
    contribution_id    TEXT PRIMARY KEY,
    username           TEXT NOT NULL,
    conjectures_attempted INTEGER NOT NULL DEFAULT 0,
    conjectures_proved    INTEGER NOT NULL DEFAULT 0,
    total_cost_usd     REAL NOT NULL DEFAULT 0,
    archive_sha256     TEXT NOT NULL DEFAULT '',
    nft_metadata       TEXT,
    prover             TEXT NOT NULL DEFAULT '',
    conjecture_ids     TEXT NOT NULL DEFAULT '[]',
    archive_path       TEXT NOT NULL DEFAULT '',
    proof_status       TEXT NOT NULL DEFAULT '',
    reviewed_by        TEXT NOT NULL DEFAULT '[]',
    created_at         TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE TABLE IF NOT EXISTS reviews (
    review_id          TEXT PRIMARY KEY,
    reviewer_username  TEXT NOT NULL,
    packages_reviewed  INTEGER NOT NULL DEFAULT 0,
    conjectures_compared INTEGER NOT NULL DEFAULT 0,
    package_rankings   TEXT NOT NULL DEFAULT '[]',
    recommendation     TEXT NOT NULL DEFAULT '',
    archive_sha256     TEXT NOT NULL DEFAULT '',
    nft_metadata       TEXT,
    created_at         TEXT NOT NULL DEFAULT (datetime('now'))
);
