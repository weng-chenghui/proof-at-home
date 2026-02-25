package integration

import (
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"strings"
	"testing"
)

// baseURL returns the server URL for integration tests.
// Set TEST_SERVER_URL to override (default: http://localhost:8080).
func baseURL() string {
	if u := os.Getenv("TEST_SERVER_URL"); u != "" {
		return u
	}
	return "http://localhost:8080"
}

func get(t *testing.T, path string) []byte {
	t.Helper()
	resp, err := http.Get(baseURL() + path)
	if err != nil {
		t.Fatalf("GET %s: %v", path, err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("GET %s: status %d", path, resp.StatusCode)
	}
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("GET %s: reading body: %v", path, err)
	}
	return body
}

func getJSON(t *testing.T, path string, v any) {
	t.Helper()
	body := get(t, path)
	if err := json.Unmarshal(body, v); err != nil {
		t.Fatalf("GET %s: unmarshal: %v\nbody: %s", path, err, body)
	}
}

// ── Health ──

func TestHealth(t *testing.T) {
	var resp struct {
		Status string `json:"status"`
	}
	getJSON(t, "/health", &resp)
	if resp.Status != "ok" {
		t.Errorf("health status = %q, want %q", resp.Status, "ok")
	}
}

// ── Conjectures ──

type conjecture struct {
	ID         string `json:"id"`
	Title      string `json:"title"`
	Difficulty string `json:"difficulty"`
	Prover     string `json:"prover"`
	Status     string `json:"status"`
}

func TestConjectures_Count(t *testing.T) {
	var conjectures []conjecture
	getJSON(t, "/conjectures", &conjectures)
	if got := len(conjectures); got != 3 {
		t.Errorf("len(conjectures) = %d, want 3", got)
	}
}

func TestConjectures_ProverField(t *testing.T) {
	var conjectures []conjecture
	getJSON(t, "/conjectures", &conjectures)

	want := map[string]string{
		"prob_001": "rocq",
		"prob_002": "rocq",
		"prob_003": "lean4",
	}
	for _, c := range conjectures {
		if exp, ok := want[c.ID]; ok {
			if c.Prover != exp {
				t.Errorf("conjecture %s: prover = %q, want %q", c.ID, c.Prover, exp)
			}
		}
	}
}

func TestConjectures_GetByID(t *testing.T) {
	var c conjecture
	getJSON(t, "/conjectures/prob_001", &c)
	if c.ID != "prob_001" {
		t.Errorf("id = %q, want %q", c.ID, "prob_001")
	}
	if c.Title == "" {
		t.Error("title is empty")
	}
}

// ── Contributions ──

type contribution struct {
	Username             string   `json:"username"`
	ContributionID       string   `json:"contribution_id"`
	ConjecturesAttempted int      `json:"conjectures_attempted"`
	ConjecturesProved    int      `json:"conjectures_proved"`
	Prover               string   `json:"prover"`
	ConjectureIDs        []string `json:"conjecture_ids"`
	ProofStatus          string   `json:"proof_status"`
	CertifiedBy          []string `json:"certified_by"`
}

func TestContributions(t *testing.T) {
	var contributions []contribution
	getJSON(t, "/contributions", &contributions)
	if len(contributions) != 1 {
		t.Fatalf("len(contributions) = %d, want 1", len(contributions))
	}
	c := contributions[0]
	if c.ContributionID != "a1111111-1111-1111-1111-111111111111" {
		t.Errorf("contribution_id = %q", c.ContributionID)
	}
	if c.Username != "alice" {
		t.Errorf("username = %q, want %q", c.Username, "alice")
	}
	if c.ConjecturesProved != 2 {
		t.Errorf("conjectures_proved = %d, want 2", c.ConjecturesProved)
	}
	if c.Prover != "rocq" {
		t.Errorf("prover = %q, want %q", c.Prover, "rocq")
	}
}

func TestContributions_Results(t *testing.T) {
	var results []struct {
		ConjectureID string `json:"conjecture_id"`
		Success      bool   `json:"success"`
	}
	getJSON(t, "/contributions/a1111111-1111-1111-1111-111111111111/results", &results)
	if len(results) != 2 {
		t.Fatalf("len(results) = %d, want 2", len(results))
	}
	for _, r := range results {
		if !r.Success {
			t.Errorf("result for %s: success = false", r.ConjectureID)
		}
	}
}

// ── Certificates ──

func TestCertificates(t *testing.T) {
	var certs []struct {
		CertificateID     string `json:"certificate_id"`
		CertifierUsername string `json:"certifier_username"`
		PackagesCertified int    `json:"packages_certified"`
	}
	getJSON(t, "/certificates", &certs)
	if len(certs) != 1 {
		t.Fatalf("len(certificates) = %d, want 1", len(certs))
	}
	if certs[0].CertificateID != "cert-demo-001" {
		t.Errorf("certificate_id = %q", certs[0].CertificateID)
	}
	if certs[0].CertifierUsername != "certifier-bot" {
		t.Errorf("certifier_username = %q", certs[0].CertifierUsername)
	}
}

// ── Certificate Packages ──

func TestCertificatePackages(t *testing.T) {
	var pkgs []struct {
		ContributorContributionID string   `json:"contributor_contribution_id"`
		ContributorUsername       string   `json:"contributor_username"`
		Prover               string   `json:"prover"`
		ConjectureIDs        []string `json:"conjecture_ids"`
		CertifiedBy          []string `json:"certified_by"`
	}
	getJSON(t, "/certificate-packages", &pkgs)
	if len(pkgs) != 1 {
		t.Fatalf("len(packages) = %d, want 1", len(pkgs))
	}
	p := pkgs[0]
	if p.ContributorUsername != "alice" {
		t.Errorf("contributor_username = %q, want %q", p.ContributorUsername, "alice")
	}
	if p.Prover != "rocq" {
		t.Errorf("prover = %q, want %q", p.Prover, "rocq")
	}
	if len(p.CertifiedBy) == 0 {
		t.Error("certified_by is empty, expected certifier-bot")
	}
}

// ── Certificate Packages: verify contributor_* JSON keys (not prover_*) ──

func TestCertificatePackages_ContributorKeys(t *testing.T) {
	body := get(t, "/certificate-packages")
	// The response should contain "contributor_contribution_id" and "contributor_username"
	if !strings.Contains(string(body), "contributor_contribution_id") {
		t.Error("response missing contributor_contribution_id key")
	}
	if !strings.Contains(string(body), "contributor_username") {
		t.Error("response missing contributor_username key")
	}
	// Should NOT contain the old prover_* keys
	if strings.Contains(string(body), "prover_contribution_id") {
		t.Error("response still contains old prover_contribution_id key")
	}
	if strings.Contains(string(body), "prover_username") {
		t.Error("response still contains old prover_username key")
	}
}

// ── 404 behavior ──

func TestConjectures_NotFound(t *testing.T) {
	resp, err := http.Get(fmt.Sprintf("%s/conjectures/nonexistent", baseURL()))
	if err != nil {
		t.Fatalf("GET: %v", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusNotFound {
		t.Errorf("status = %d, want 404", resp.StatusCode)
	}
}
