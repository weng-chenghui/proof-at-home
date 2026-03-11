-- Add credits_json column to lessons and series for CREDITS.toml data
ALTER TABLE lessons ADD COLUMN credits_json TEXT NOT NULL DEFAULT '';
ALTER TABLE series ADD COLUMN credits_json TEXT NOT NULL DEFAULT '';
