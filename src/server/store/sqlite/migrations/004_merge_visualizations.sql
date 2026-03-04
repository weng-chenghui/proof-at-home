-- Add visualization-specific columns to expositions
ALTER TABLE expositions ADD COLUMN domain TEXT NOT NULL DEFAULT '';
ALTER TABLE expositions ADD COLUMN title TEXT NOT NULL DEFAULT '';
ALTER TABLE expositions ADD COLUMN summary TEXT NOT NULL DEFAULT '';

-- Migrate existing visualization data into expositions
INSERT OR IGNORE INTO expositions (
    exposition_id, author_username, contribution_id, conjecture_id,
    prover, proof_script, exposition_text, cost_usd, strategy_used,
    nft_metadata, created_at, domain, title, summary
)
SELECT
    visualization_id, author_username, '', conjecture_id,
    '', '', viz_json, cost_usd, strategy_used,
    nft_metadata, created_at, domain, title, summary
FROM visualizations;

-- Drop the visualizations table
DROP TABLE IF EXISTS visualizations;
