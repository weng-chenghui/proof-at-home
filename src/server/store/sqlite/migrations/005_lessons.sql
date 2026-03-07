CREATE TABLE IF NOT EXISTS lessons (
    lesson_id       TEXT PRIMARY KEY,
    author_username TEXT NOT NULL,
    title           TEXT NOT NULL DEFAULT '',
    topic           TEXT NOT NULL DEFAULT '',
    difficulty      TEXT NOT NULL DEFAULT '',
    description     TEXT NOT NULL DEFAULT '',
    prerequisites   TEXT NOT NULL DEFAULT '',
    conjecture_ids  TEXT NOT NULL DEFAULT '[]',
    published       INTEGER NOT NULL DEFAULT 0,
    created_at      TEXT NOT NULL DEFAULT (datetime('now'))
);
