package gitstore

// ForgeClient abstracts Git forge operations (GitHub, GitLab, etc.)
// so that GitStore can create PRs without knowing which forge it's talking to.
type ForgeClient interface {
	// CreatePR creates a pull/merge request from branch to base.
	// Returns the web URL of the created PR/MR.
	CreatePR(branch, base, title, body string) (prURL string, err error)

	// VerifyWebhookSignature verifies the signature of a webhook payload.
	// For GitHub: HMAC-SHA256 of body vs X-Hub-Signature-256 header.
	// For GitLab: compare X-Gitlab-Token header against configured secret.
	VerifyWebhookSignature(payload []byte, signature string) bool

	// RepoURL returns the web URL of the data repository
	// (e.g. "https://github.com/org/proof-at-home-data").
	RepoURL() string
}
