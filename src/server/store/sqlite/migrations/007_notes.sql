CREATE TABLE IF NOT EXISTS notes (
    note_id         TEXT PRIMARY KEY,
    lesson_id       TEXT NOT NULL,
    content_hash    TEXT NOT NULL DEFAULT '',
    anchor_text     TEXT NOT NULL DEFAULT '',
    line_start      INTEGER NOT NULL DEFAULT 0,
    line_end        INTEGER NOT NULL DEFAULT 0,
    content         TEXT NOT NULL DEFAULT '',
    highlight_color TEXT NOT NULL DEFAULT '#FFE082',
    user_id         TEXT NOT NULL DEFAULT '',
    username        TEXT NOT NULL DEFAULT '',
    status          TEXT NOT NULL DEFAULT 'active',
    created_at      TEXT NOT NULL DEFAULT (datetime('now')),
    updated_at      TEXT NOT NULL DEFAULT (datetime('now'))
);
CREATE INDEX IF NOT EXISTS idx_notes_lesson_id ON notes (lesson_id);
CREATE INDEX IF NOT EXISTS idx_notes_user_id ON notes (user_id);
