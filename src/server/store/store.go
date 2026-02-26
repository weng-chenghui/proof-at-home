package store

import "github.com/proof-at-home/server/src/server/data"

// Store defines the read-only cache interface.
// All writes go through GitStore; the cache is rebuilt from git content on webhook events.
type Store interface {
	ListConjectures() []data.ConjectureSummary
	GetConjecture(id string) (data.Conjecture, bool)
	ListContributions() []data.Contribution
	GetContribution(id string) (data.Contribution, bool)
	ListProofs(contributionID string) []data.Proof
	ListContributionReviews() []data.ContributionReview
	ListCertificates() []data.Certificate
	ListStrategies() []data.Strategy
	GetStrategy(name string) (data.Strategy, bool)
	RebuildFromDir(repoPath string) error
}
