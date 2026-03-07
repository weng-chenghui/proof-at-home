-- Add content and ai_annotations columns to lessons
ALTER TABLE lessons ADD COLUMN content TEXT NOT NULL DEFAULT '';
ALTER TABLE lessons ADD COLUMN ai_annotations TEXT NOT NULL DEFAULT '[]';

-- Create series table
CREATE TABLE IF NOT EXISTS series (
    series_id       TEXT PRIMARY KEY,
    title           TEXT NOT NULL DEFAULT '',
    author_username TEXT NOT NULL DEFAULT '',
    difficulty      TEXT NOT NULL DEFAULT '',
    description     TEXT NOT NULL DEFAULT '',
    lesson_ids      TEXT NOT NULL DEFAULT '[]',
    published       INTEGER NOT NULL DEFAULT 0,
    created_at      TEXT NOT NULL DEFAULT (datetime('now')),
    content         TEXT NOT NULL DEFAULT ''
);
