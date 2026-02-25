package store

import "github.com/proof-at-home/server/src/server/data"

// Store defines the read-only cache interface.
// All writes go through GitStore; the cache is rebuilt from git content on webhook events.
type Store interface {
	ListConjectures() []data.ConjectureSummary
	GetConjecture(id string) (data.Conjecture, bool)
	ListContributions() []data.ContributionSummary
	GetContribution(id string) (data.ContributionSummary, bool)
	ListContributionResults(contributionID string) []data.ContributionResult
	ListCertificatePackages() []data.CertificatePackageInfo
	ListCertificates() []data.CertificateSummary
	ListCommands() []data.Command
	GetCommand(name string) (data.Command, bool)
	RebuildFromDir(repoPath string) error
}
