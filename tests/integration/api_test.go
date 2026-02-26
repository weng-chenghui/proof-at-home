package integration

import (
	"bytes"
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
	if len(contributions) < 1 {
		t.Fatalf("len(contributions) = %d, want >= 1", len(contributions))
	}
	// Find the seed contribution by ID (write tests may add more)
	var found bool
	for _, c := range contributions {
		if c.ContributionID == "a1111111-1111-1111-1111-111111111111" {
			found = true
			if c.Username != "alice" {
				t.Errorf("username = %q, want %q", c.Username, "alice")
			}
			if c.ConjecturesProved != 2 {
				t.Errorf("conjectures_proved = %d, want 2", c.ConjecturesProved)
			}
			if c.Prover != "rocq" {
				t.Errorf("prover = %q, want %q", c.Prover, "rocq")
			}
			break
		}
	}
	if !found {
		t.Error("seed contribution a1111111-1111-1111-1111-111111111111 not found")
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
	if len(certs) < 1 {
		t.Fatalf("len(certificates) = %d, want >= 1", len(certs))
	}
	// Find the seed certificate by ID (write tests may add more)
	var found bool
	for _, c := range certs {
		if c.CertificateID == "cert-demo-001" {
			found = true
			if c.CertifierUsername != "certifier-bot" {
				t.Errorf("certifier_username = %q", c.CertifierUsername)
			}
			break
		}
	}
	if !found {
		t.Error("seed certificate cert-demo-001 not found")
	}
}

// ── Certificate Packages ──

func TestCertificatePackages(t *testing.T) {
	var pkgs []struct {
		ContributorContributionID string   `json:"contributor_contribution_id"`
		ContributorUsername       string   `json:"contributor_username"`
		Prover                    string   `json:"prover"`
		ConjectureIDs             []string `json:"conjecture_ids"`
		CertifiedBy               []string `json:"certified_by"`
	}
	getJSON(t, "/certificate-packages", &pkgs)
	if len(pkgs) < 1 {
		t.Fatalf("len(packages) = %d, want >= 1", len(pkgs))
	}
	// Find alice's seed package (write tests may add more)
	var found bool
	for _, p := range pkgs {
		if p.ContributorUsername == "alice" {
			found = true
			if p.Prover != "rocq" {
				t.Errorf("prover = %q, want %q", p.Prover, "rocq")
			}
			if len(p.CertifiedBy) == 0 {
				t.Error("certified_by is empty, expected certifier-bot")
			}
			break
		}
	}
	if !found {
		t.Error("seed package for alice not found")
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

// ── Write-path tests ──

func postJSON(t *testing.T, path string, body any) (int, map[string]any) {
	t.Helper()
	b, err := json.Marshal(body)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	resp, err := http.Post(baseURL()+path, "application/json", bytes.NewReader(b))
	if err != nil {
		t.Fatalf("POST %s: %v", path, err)
	}
	defer resp.Body.Close()
	raw, _ := io.ReadAll(resp.Body)
	var result map[string]any
	json.Unmarshal(raw, &result)
	return resp.StatusCode, result
}

func patchJSON(t *testing.T, path string, body any) (int, map[string]any) {
	t.Helper()
	b, err := json.Marshal(body)
	if err != nil {
		t.Fatalf("marshal: %v", err)
	}
	req, err := http.NewRequest("PATCH", baseURL()+path, bytes.NewReader(b))
	if err != nil {
		t.Fatalf("PATCH %s: %v", path, err)
	}
	req.Header.Set("Content-Type", "application/json")
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("PATCH %s: %v", path, err)
	}
	defer resp.Body.Close()
	raw, _ := io.ReadAll(resp.Body)
	var result map[string]any
	json.Unmarshal(raw, &result)
	return resp.StatusCode, result
}

func TestCreateContribution(t *testing.T) {
	body := map[string]any{
		"username":              "test-user",
		"contribution_id":       "test-contrib-001",
		"conjectures_attempted": 1,
		"conjectures_proved":    0,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001"},
	}
	status, resp := postJSON(t, "/contributions", body)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions: status %d, body %v", status, resp)
	}
	if resp["status"] != "accepted" {
		t.Errorf("status = %q, want %q", resp["status"], "accepted")
	}
}

func TestSubmitResult(t *testing.T) {
	// First create a contribution
	body := map[string]any{
		"username":              "test-user-result",
		"contribution_id":       "test-contrib-result-001",
		"conjectures_attempted": 1,
		"conjectures_proved":    0,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001"},
	}
	status, _ := postJSON(t, "/contributions", body)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions: status %d", status)
	}

	// Then submit a result
	result := map[string]any{
		"conjecture_id": "prob_001",
		"username":      "test-user-result",
		"success":       true,
		"proof_script":  "Proof. auto. Qed.",
		"cost_usd":      0.01,
		"attempts":      1,
	}
	status, resp := postJSON(t, "/contributions/test-contrib-result-001/results", result)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions/{id}/results: status %d, body %v", status, resp)
	}
	if resp["status"] != "accepted" {
		t.Errorf("status = %q, want %q", resp["status"], "accepted")
	}
}

func TestFinalizeContribution(t *testing.T) {
	// Create a contribution
	body := map[string]any{
		"username":              "test-user-finalize",
		"contribution_id":       "test-contrib-finalize-001",
		"conjectures_attempted": 1,
		"conjectures_proved":    1,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001"},
	}
	status, _ := postJSON(t, "/contributions", body)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions: status %d", status)
	}

	// Finalize it
	finalize := map[string]any{
		"username":              "test-user-finalize",
		"contribution_id":       "test-contrib-finalize-001",
		"conjectures_attempted": 1,
		"conjectures_proved":    1,
		"total_cost_usd":        0.05,
		"proof_status":          "complete",
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001"},
	}
	status, resp := patchJSON(t, "/contributions/test-contrib-finalize-001", finalize)
	if status != http.StatusOK {
		t.Fatalf("PATCH /contributions/{id}: status %d, body %v", status, resp)
	}
	if _, ok := resp["commit_sha"]; !ok {
		t.Error("response missing commit_sha")
	}
}

func TestSealContribution(t *testing.T) {
	// Create and finalize a contribution
	body := map[string]any{
		"username":              "test-user-seal",
		"contribution_id":       "test-contrib-seal-001",
		"conjectures_attempted": 1,
		"conjectures_proved":    1,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001"},
	}
	postJSON(t, "/contributions", body)
	patchJSON(t, "/contributions/test-contrib-seal-001", body)

	// Seal it
	nft := map[string]any{
		"name":        "Test NFT",
		"description": "Test contribution NFT",
	}
	status, resp := postJSON(t, "/contributions/test-contrib-seal-001/seal", nft)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions/{id}/seal: status %d, body %v", status, resp)
	}
	if _, ok := resp["pr_url"]; !ok {
		t.Error("response missing pr_url")
	}
}

func TestCreateCertificate(t *testing.T) {
	body := map[string]any{
		"certifier_username":   "test-certifier",
		"certificate_id":       "test-cert-001",
		"packages_certified":   1,
		"conjectures_compared": 2,
		"package_rankings":     []map[string]any{},
		"recommendation":       "approved",
	}
	status, resp := postJSON(t, "/certificates", body)
	if status != http.StatusCreated {
		t.Fatalf("POST /certificates: status %d, body %v", status, resp)
	}
	if _, ok := resp["commit_sha"]; !ok {
		t.Error("response missing commit_sha")
	}
}

func TestSealCertificate(t *testing.T) {
	// Create a certificate first
	body := map[string]any{
		"certifier_username":   "test-certifier-seal",
		"certificate_id":       "test-cert-seal-001",
		"packages_certified":   1,
		"conjectures_compared": 2,
		"package_rankings":     []map[string]any{},
		"recommendation":       "approved",
	}
	postJSON(t, "/certificates", body)

	// Seal it
	nft := map[string]any{
		"name":        "Test Cert NFT",
		"description": "Test certificate NFT",
	}
	status, resp := postJSON(t, "/certificates/test-cert-seal-001/seal", nft)
	if status != http.StatusCreated {
		t.Fatalf("POST /certificates/{id}/seal: status %d, body %v", status, resp)
	}
	if _, ok := resp["pr_url"]; !ok {
		t.Error("response missing pr_url")
	}
}

func TestWebhook_IgnoresNonMain(t *testing.T) {
	body := map[string]any{
		"ref": "refs/heads/feature",
	}
	status, resp := postJSON(t, "/webhooks/git", body)
	if status != http.StatusOK {
		t.Fatalf("POST /webhooks/git: status %d, body %v", status, resp)
	}
	if resp["status"] != "ignored" {
		t.Errorf("status = %q, want %q", resp["status"], "ignored")
	}
}

func TestArchiveDownload(t *testing.T) {
	// The archive endpoint requires proofs to exist in git.
	// For the seed data (alice's contribution), check if it has proofs.
	resp, err := http.Get(fmt.Sprintf("%s/certificate-packages/a1111111-1111-1111-1111-111111111111/archive", baseURL()))
	if err != nil {
		t.Fatalf("GET: %v", err)
	}
	defer resp.Body.Close()
	// Accept either 200 (proofs exist) or 404 (no proofs dir in seed data)
	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusNotFound {
		t.Errorf("status = %d, want 200 or 404", resp.StatusCode)
	}
	if resp.StatusCode == http.StatusOK {
		ct := resp.Header.Get("Content-Type")
		if !strings.Contains(ct, "gzip") {
			t.Errorf("content-type = %q, want gzip", ct)
		}
	}
}

// ── Manual proof submission flow (prove submit) ──

func TestManualProofContribution(t *testing.T) {
	contribID := "test-manual-contrib-001"

	// 1. Create draft contribution
	create := map[string]any{
		"username":              "manual-prover",
		"contribution_id":       contribID,
		"conjectures_attempted": 0,
		"conjectures_proved":    0,
	}
	status, _ := postJSON(t, "/contributions", create)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions: status %d", status)
	}

	// 2. Submit a proof result with cost_usd = 0 (manual mode)
	result := map[string]any{
		"conjecture_id": "prob_001",
		"username":      "manual-prover",
		"success":       true,
		"proof_script":  "Lemma add_comm : forall n m : nat, n + m = m + n.\nProof.\n  intros n m. lia.\nQed.",
		"cost_usd":      0.0,
		"attempts":      1,
	}
	status, resp := postJSON(t, fmt.Sprintf("/contributions/%s/results", contribID), result)
	if status != http.StatusCreated {
		t.Fatalf("POST results: status %d, body %v", status, resp)
	}

	// 3. Finalize with total_cost_usd = 0
	finalize := map[string]any{
		"username":              "manual-prover",
		"contribution_id":       contribID,
		"conjectures_attempted": 1,
		"conjectures_proved":    1,
		"total_cost_usd":        0.0,
		"proof_status":          "proved",
	}
	status, resp = patchJSON(t, fmt.Sprintf("/contributions/%s", contribID), finalize)
	if status != http.StatusOK {
		t.Fatalf("PATCH finalize: status %d, body %v", status, resp)
	}
	if _, ok := resp["commit_sha"]; !ok {
		t.Error("finalize response missing commit_sha")
	}

	// 4. Seal with NFT metadata containing Proof Mode: manual
	nft := map[string]any{
		"name":        "Proof@Home Contribution — manual-prover — 2026-02-26",
		"description": "Formally verified mathematical proofs for the public domain.",
		"attributes": []map[string]any{
			{"trait_type": "Username", "value": "manual-prover"},
			{"trait_type": "Conjectures Proved", "value": 1},
			{"trait_type": "Conjectures Attempted", "value": 1},
			{"trait_type": "Cost Donated (USD)", "value": "0.00"},
			{"trait_type": "Proof Status", "value": "proved"},
			{"trait_type": "Proof Mode", "value": "manual"},
		},
	}
	status, resp = postJSON(t, fmt.Sprintf("/contributions/%s/seal", contribID), nft)
	if status != http.StatusCreated {
		t.Fatalf("POST seal: status %d, body %v", status, resp)
	}
	if _, ok := resp["pr_url"]; !ok {
		t.Error("seal response missing pr_url")
	}
}

func TestManualProofContribution_ZeroCostResult(t *testing.T) {
	contribID := "test-manual-zerocost-001"

	// Create contribution and submit a result with zero cost
	create := map[string]any{
		"username":              "manual-prover-2",
		"contribution_id":       contribID,
		"conjectures_attempted": 0,
		"conjectures_proved":    0,
	}
	status, _ := postJSON(t, "/contributions", create)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions: status %d", status)
	}

	result := map[string]any{
		"conjecture_id": "prob_001",
		"username":      "manual-prover-2",
		"success":       true,
		"proof_script":  "Proof. lia. Qed.",
		"cost_usd":      0.0,
		"attempts":      1,
	}
	status, resp := postJSON(t, fmt.Sprintf("/contributions/%s/results", contribID), result)
	if status != http.StatusCreated {
		t.Fatalf("POST results: status %d, body %v", status, resp)
	}
	if resp["status"] != "accepted" {
		t.Errorf("status = %q, want %q", resp["status"], "accepted")
	}
}

// ── Commands ──

func TestCommands_List(t *testing.T) {
	var commands []struct {
		Name        string `json:"name"`
		Kind        string `json:"kind"`
		Prover      string `json:"prover"`
		Description string `json:"description"`
	}
	getJSON(t, "/commands", &commands)
	if got := len(commands); got != 4 {
		t.Errorf("len(commands) = %d, want 4", got)
	}
}

func TestCommands_GetByName(t *testing.T) {
	var cmd struct {
		Name        string `json:"name"`
		Kind        string `json:"kind"`
		Prover      string `json:"prover"`
		Description string `json:"description"`
		Body        string `json:"body"`
	}
	getJSON(t, "/commands/prove-coq-lemma", &cmd)
	if cmd.Name != "prove-coq-lemma" {
		t.Errorf("name = %q, want %q", cmd.Name, "prove-coq-lemma")
	}
	if cmd.Kind != "prove" {
		t.Errorf("kind = %q, want %q", cmd.Kind, "prove")
	}
	if cmd.Prover != "rocq" {
		t.Errorf("prover = %q, want %q", cmd.Prover, "rocq")
	}
	if cmd.Body == "" {
		t.Error("body is empty")
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
