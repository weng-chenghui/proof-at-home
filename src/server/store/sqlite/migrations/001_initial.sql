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

CREATE TABLE IF NOT EXISTS proofs (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    contribution_id TEXT NOT NULL DEFAULT '',
    conjecture_id TEXT NOT NULL,
    username     TEXT NOT NULL,
    success      INTEGER NOT NULL DEFAULT 0,
    proof_script TEXT NOT NULL DEFAULT '',
    cost_usd     REAL NOT NULL DEFAULT 0,
    attempts     INTEGER NOT NULL DEFAULT 0,
    error_output TEXT NOT NULL DEFAULT '',
    created_at   TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE INDEX IF NOT EXISTS idx_proofs_conjecture_id ON proofs(conjecture_id);
CREATE INDEX IF NOT EXISTS idx_proofs_username ON proofs(username);
CREATE INDEX IF NOT EXISTS idx_proofs_contribution_id ON proofs(contribution_id);

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
    certified_by       TEXT NOT NULL DEFAULT '[]',
    created_at         TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE TABLE IF NOT EXISTS certificates (
    certificate_id     TEXT PRIMARY KEY,
    certifier_username TEXT NOT NULL,
    packages_certified INTEGER NOT NULL DEFAULT 0,
    conjectures_compared INTEGER NOT NULL DEFAULT 0,
    package_rankings   TEXT NOT NULL DEFAULT '[]',
    recommendation     TEXT NOT NULL DEFAULT '',
    archive_sha256     TEXT NOT NULL DEFAULT '',
    nft_metadata       TEXT,
    created_at         TEXT NOT NULL DEFAULT (datetime('now'))
);

CREATE TABLE IF NOT EXISTS strategies (
    name        TEXT PRIMARY KEY,
    kind        TEXT NOT NULL DEFAULT 'prove',
    prover      TEXT NOT NULL DEFAULT '',
    description TEXT NOT NULL DEFAULT '',
    priority    INTEGER NOT NULL DEFAULT 0,
    body        TEXT NOT NULL DEFAULT ''
);

