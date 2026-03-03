CREATE TABLE IF NOT EXISTS expositions (
    exposition_id    TEXT PRIMARY KEY,
    author_username  TEXT NOT NULL,
    contribution_id  TEXT NOT NULL DEFAULT '',
    conjecture_id    TEXT NOT NULL DEFAULT '',
    prover           TEXT NOT NULL DEFAULT '',
    proof_script     TEXT NOT NULL DEFAULT '',
    exposition_text  TEXT NOT NULL DEFAULT '',
    cost_usd         REAL NOT NULL DEFAULT 0,
    strategy_used    TEXT NOT NULL DEFAULT '',
    nft_metadata     TEXT,
    created_at       TEXT NOT NULL DEFAULT (datetime('now'))
);
