package main

import (
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"os"

	"github.com/proof-at-home/server/src/server/handlers"
	"github.com/proof-at-home/server/src/server/store"
)

func main() {
	port := "8080"
	if p := os.Getenv("PORT"); p != "" {
		port = p
	}

	problemsDir := "problems"
	if d := os.Getenv("PROBLEMS_DIR"); d != "" {
		problemsDir = d
	}

	s := store.NewMemoryStore()
	if err := s.LoadProblems(problemsDir); err != nil {
		log.Fatalf("Failed to load problems: %v", err)
	}

	problemHandler := &handlers.ProblemHandler{Store: s}
	resultHandler := &handlers.ResultHandler{Store: s}
	reviewHandler := &handlers.ReviewHandler{Store: s}

	http.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]string{"status": "ok"})
	})

	packageHandler := &handlers.PackageHandler{Store: s}
	http.Handle("/problems/packages", packageHandler)

	http.Handle("/problems/", problemHandler)
	http.Handle("/problems", problemHandler)

	http.HandleFunc("/results/batch", resultHandler.HandleBatch)
	http.HandleFunc("/results", resultHandler.HandleResult)

	http.Handle("/review-packages/", reviewHandler)
	http.Handle("/review-packages", reviewHandler)
	http.HandleFunc("/reviews", reviewHandler.HandleSubmitReview)

	// Optionally seed demo review data
	if os.Getenv("SEED_REVIEWS") != "" {
		seedDir := os.Getenv("SEED_REVIEWS")
		if err := s.LoadSeedSessions(seedDir); err != nil {
			log.Printf("Warning: failed to load seed review data: %v", err)
		} else {
			fmt.Printf("Seed review data loaded from %s/\n", seedDir)
		}
	}

	fmt.Printf("Proof@Home server listening on :%s\n", port)
	fmt.Printf("Problems loaded from %s/\n", problemsDir)
	log.Fatal(http.ListenAndServe(":"+port, nil))
}
