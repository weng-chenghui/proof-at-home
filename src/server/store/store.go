package store

import "github.com/proof-at-home/server/src/server/data"

// Store defines the runtime storage interface for the proof-at-home server.
// LoadProblems and LoadSeedSessions are startup-only and not part of this interface.
type Store interface {
	ListProblems() []data.ProblemSummary
	GetProblem(id string) (data.Problem, bool)
	AddProblems(problems []data.Problem) []string
	AddResult(r data.ProofResult)
	AddSession(ss data.SessionSummary)
	ListReviewPackages() []data.ReviewPackageInfo
	GetArchivePath(sessionID string) (string, bool)
	AddReview(r data.ReviewSummary)
}
