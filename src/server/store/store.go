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
	ListExpositions() []data.Exposition
	GetExposition(id string) (data.Exposition, bool)
	ListLessons() []data.Lesson
	GetLesson(id string) (data.Lesson, bool)
	ListSeries() []data.Series
	GetSeries(id string) (data.Series, bool)
	ListNotes(lessonID string) []data.Note
	GetNote(noteID string) (data.Note, bool)
	CreateNote(note data.Note) error
	UpdateNote(note data.Note) error
	DeleteNote(noteID string) error
	ListAllNotes() []data.Note
	RebuildFromDir(repoPath string) error
}
