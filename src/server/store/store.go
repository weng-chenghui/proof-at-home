package store

import "github.com/proof-at-home/server/src/server/data"

// Store defines the runtime storage interface for the proof-at-home server.
// LoadConjectures and LoadSeedContributions are startup-only and not part of this interface.
type Store interface {
	ListConjectures() []data.ConjectureSummary
	GetConjecture(id string) (data.Conjecture, bool)
	AddConjectures(conjectures []data.Conjecture) []string
	AddContributionResult(r data.ContributionResult)
	AddContribution(cs data.ContributionSummary)
	ListCertificatePackages() []data.CertificatePackageInfo
	GetArchivePath(contributionID string) (string, bool)
	AddCertificate(r data.CertificateSummary)
}
