CREATE TABLE IF NOT EXISTS visualizations (
    visualization_id TEXT PRIMARY KEY,
    author_username  TEXT NOT NULL,
    conjecture_id    TEXT NOT NULL DEFAULT '',
    domain           TEXT NOT NULL DEFAULT '',
    title            TEXT NOT NULL DEFAULT '',
    summary          TEXT NOT NULL DEFAULT '',
    viz_json         TEXT NOT NULL DEFAULT '{}',
    cost_usd         REAL NOT NULL DEFAULT 0,
    strategy_used    TEXT NOT NULL DEFAULT '',
    nft_metadata     TEXT,
    created_at       TEXT NOT NULL DEFAULT (datetime('now'))
);
