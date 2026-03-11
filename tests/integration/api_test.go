package integration

import (
	"archive/tar"
	"bytes"
	"compress/gzip"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
	"testing"
	"time"
)

var httpClient = &http.Client{Timeout: 30 * time.Second}

func get(t *testing.T, path string) []byte {
	t.Helper()
	resp, err := httpClient.Get(serverURL + path)
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

// waitFor polls f every 200ms until it returns true or timeout elapses.
func waitFor(t *testing.T, timeout time.Duration, desc string, f func() bool) {
	t.Helper()
	deadline := time.Now().Add(timeout)
	for time.Now().Before(deadline) {
		if f() {
			return
		}
		time.Sleep(200 * time.Millisecond)
	}
	t.Fatalf("timed out waiting for: %s", desc)
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
	if got := len(conjectures); got < 3 {
		t.Errorf("len(conjectures) = %d, want at least 3", got)
	}
}

func TestConjectures_ProverField(t *testing.T) {
	var conjectures []conjecture
	getJSON(t, "/conjectures", &conjectures)

	want := map[string]string{
		"prob_001_rocq": "rocq",
		"prob_002_rocq": "rocq",
		"prob_003_lean4": "lean4",
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
	getJSON(t, "/conjectures/prob_001_rocq", &c)
	if c.ID != "prob_001_rocq" {
		t.Errorf("id = %q, want %q", c.ID, "prob_001_rocq")
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
	getJSON(t, "/contributions/a1111111-1111-1111-1111-111111111111/proofs", &results)
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
	getJSON(t, "/contribution-reviews", &pkgs)
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
	body := get(t, "/contribution-reviews")
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
	resp, err := httpClient.Post(serverURL+path, "application/json", bytes.NewReader(b))
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
	req, err := http.NewRequest("PATCH", serverURL+path, bytes.NewReader(b))
	if err != nil {
		t.Fatalf("PATCH %s: %v", path, err)
	}
	req.Header.Set("Content-Type", "application/json")
	resp, err := httpClient.Do(req)
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
	contribID := fmt.Sprintf("test-contrib-%d", time.Now().UnixNano())
	body := map[string]any{
		"username":              "test-user",
		"contribution_id":       contribID,
		"conjectures_attempted": 1,
		"conjectures_proved":    0,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001_rocq"},
	}
	status, resp := postJSON(t, "/contributions", body)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions: status %d, body %v", status, resp)
	}
	if resp["status"] != "accepted" {
		t.Errorf("status = %q, want %q", resp["status"], "accepted")
	}
}

func TestSubmitProof(t *testing.T) {
	contribID := fmt.Sprintf("test-result-%d", time.Now().UnixNano())
	// First create a contribution
	body := map[string]any{
		"username":              "test-user-result",
		"contribution_id":       contribID,
		"conjectures_attempted": 1,
		"conjectures_proved":    0,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001_rocq"},
	}
	status, _ := postJSON(t, "/contributions", body)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions: status %d", status)
	}

	// Then submit a result
	result := map[string]any{
		"conjecture_id": "prob_001_rocq",
		"username":      "test-user-result",
		"success":       true,
		"proof_script":  "Proof. auto. Qed.",
		"cost_usd":      0.01,
		"attempts":      1,
	}
	status, resp := postJSON(t, fmt.Sprintf("/contributions/%s/proofs", contribID), result)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions/{id}/proofs: status %d, body %v", status, resp)
	}
	if resp["status"] != "accepted" {
		t.Errorf("status = %q, want %q", resp["status"], "accepted")
	}
}

func TestFinalizeContribution(t *testing.T) {
	contribID := fmt.Sprintf("test-finalize-%d", time.Now().UnixNano())
	// Create a contribution
	body := map[string]any{
		"username":              "test-user-finalize",
		"contribution_id":       contribID,
		"conjectures_attempted": 1,
		"conjectures_proved":    1,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001_rocq"},
	}
	status, _ := postJSON(t, "/contributions", body)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions: status %d", status)
	}

	// Finalize it
	finalize := map[string]any{
		"username":              "test-user-finalize",
		"contribution_id":       contribID,
		"conjectures_attempted": 1,
		"conjectures_proved":    1,
		"total_cost_usd":        0.05,
		"proof_status":          "complete",
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001_rocq"},
	}
	status, resp := patchJSON(t, fmt.Sprintf("/contributions/%s", contribID), finalize)
	if status != http.StatusOK {
		t.Fatalf("PATCH /contributions/{id}: status %d, body %v", status, resp)
	}
	if _, ok := resp["commit_sha"]; !ok {
		t.Error("response missing commit_sha")
	}
}

func TestSealContribution(t *testing.T) {
	contribID := fmt.Sprintf("test-seal-%d", time.Now().UnixNano())
	// Create and finalize a contribution
	body := map[string]any{
		"username":              "test-user-seal",
		"contribution_id":       contribID,
		"conjectures_attempted": 1,
		"conjectures_proved":    1,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001_rocq"},
	}
	postJSON(t, "/contributions", body)
	patchJSON(t, fmt.Sprintf("/contributions/%s", contribID), body)

	// Seal it
	nft := map[string]any{
		"name":        "Test NFT",
		"description": "Test contribution NFT",
	}
	status, resp := postJSON(t, fmt.Sprintf("/contributions/%s/seal", contribID), nft)
	if status != http.StatusCreated {
		t.Fatalf("POST /contributions/{id}/seal: status %d, body %v", status, resp)
	}
	if _, ok := resp["pr_url"]; !ok {
		t.Error("response missing pr_url")
	}
}

func TestCreateCertificate(t *testing.T) {
	certID := fmt.Sprintf("test-cert-%d", time.Now().UnixNano())
	body := map[string]any{
		"certifier_username":   "test-certifier",
		"certificate_id":       certID,
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
	certID := fmt.Sprintf("test-cert-seal-%d", time.Now().UnixNano())
	// Create a certificate first
	body := map[string]any{
		"certifier_username":   "test-certifier-seal",
		"certificate_id":       certID,
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
	status, resp := postJSON(t, fmt.Sprintf("/certificates/%s/seal", certID), nft)
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
	resp, err := httpClient.Get(fmt.Sprintf("%s/contributions/a1111111-1111-1111-1111-111111111111/archive", serverURL))
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
	contribID := fmt.Sprintf("test-manual-%d", time.Now().UnixNano())

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
		"conjecture_id": "prob_001_rocq",
		"username":      "manual-prover",
		"success":       true,
		"proof_script":  "Lemma add_comm : forall n m : nat, n + m = m + n.\nProof.\n  intros n m. lia.\nQed.",
		"cost_usd":      0.0,
		"attempts":      1,
	}
	status, resp := postJSON(t, fmt.Sprintf("/contributions/%s/proofs", contribID), result)
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
	contribID := fmt.Sprintf("test-zerocost-%d", time.Now().UnixNano())

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
		"conjecture_id": "prob_001_rocq",
		"username":      "manual-prover-2",
		"success":       true,
		"proof_script":  "Proof. lia. Qed.",
		"cost_usd":      0.0,
		"attempts":      1,
	}
	status, resp := postJSON(t, fmt.Sprintf("/contributions/%s/proofs", contribID), result)
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
	getJSON(t, "/strategies", &commands)
	if got := len(commands); got != 5 {
		t.Errorf("len(commands) = %d, want 5", got)
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
	getJSON(t, "/strategies/prove-coq-lemma", &cmd)
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
	resp, err := httpClient.Get(fmt.Sprintf("%s/conjectures/nonexistent", serverURL))
	if err != nil {
		t.Fatalf("GET: %v", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusNotFound {
		t.Errorf("status = %d, want 404", resp.StatusCode)
	}
}

// ── Helpers for role flow tests ──

func postRaw(t *testing.T, path string, contentType string, body []byte) (int, map[string]any) {
	t.Helper()
	resp, err := httpClient.Post(serverURL+path, contentType, bytes.NewReader(body))
	if err != nil {
		t.Fatalf("POST %s: %v", path, err)
	}
	defer resp.Body.Close()
	raw, _ := io.ReadAll(resp.Body)
	var result map[string]any
	json.Unmarshal(raw, &result)
	return resp.StatusCode, result
}

func buildConjectureTarGz(t *testing.T, conjectures []map[string]any) []byte {
	t.Helper()
	var buf bytes.Buffer
	gw := gzip.NewWriter(&buf)
	tw := tar.NewWriter(gw)

	for i, c := range conjectures {
		data, err := json.Marshal(c)
		if err != nil {
			t.Fatalf("marshal conjecture %d: %v", i, err)
		}
		name := fmt.Sprintf("conjecture_%d.json", i)
		hdr := &tar.Header{
			Name: name,
			Mode: 0644,
			Size: int64(len(data)),
		}
		if err := tw.WriteHeader(hdr); err != nil {
			t.Fatalf("tar header %s: %v", name, err)
		}
		if _, err := tw.Write(data); err != nil {
			t.Fatalf("tar write %s: %v", name, err)
		}
	}

	if err := tw.Close(); err != nil {
		t.Fatalf("tar close: %v", err)
	}
	if err := gw.Close(); err != nil {
		t.Fatalf("gzip close: %v", err)
	}
	return buf.Bytes()
}

// ── Role flow happy-path tests ──

func TestContributorFlow(t *testing.T) {
	contribID := fmt.Sprintf("flow-ai-%d", time.Now().UnixNano())

	// 1. Create contribution
	create := map[string]any{
		"username":              "flow-contributor",
		"contribution_id":       contribID,
		"conjectures_attempted": 0,
		"conjectures_proved":    0,
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001_rocq"},
	}
	status, _ := postJSON(t, "/contributions", create)
	if status != http.StatusCreated {
		t.Fatalf("create contribution: status %d", status)
	}

	// 2. Submit proof with cost_usd > 0 (AI mode)
	proof := map[string]any{
		"conjecture_id": "prob_001_rocq",
		"username":      "flow-contributor",
		"success":       true,
		"proof_script":  "Proof. auto. Qed.",
		"cost_usd":      0.05,
		"attempts":      3,
	}
	status, resp := postJSON(t, fmt.Sprintf("/contributions/%s/proofs", contribID), proof)
	if status != http.StatusCreated {
		t.Fatalf("submit proof: status %d, body %v", status, resp)
	}

	// 3. Finalize with total cost
	finalize := map[string]any{
		"username":              "flow-contributor",
		"contribution_id":       contribID,
		"conjectures_attempted": 1,
		"conjectures_proved":    1,
		"total_cost_usd":        0.05,
		"proof_status":          "complete",
		"prover":                "rocq",
		"conjecture_ids":        []string{"prob_001_rocq"},
	}
	status, resp = patchJSON(t, fmt.Sprintf("/contributions/%s", contribID), finalize)
	if status != http.StatusOK {
		t.Fatalf("finalize: status %d, body %v", status, resp)
	}
	if _, ok := resp["commit_sha"]; !ok {
		t.Error("finalize response missing commit_sha")
	}

	// 4. Seal with NFT metadata (AI mode)
	nft := map[string]any{
		"name":        "Proof@Home Contribution — flow-contributor",
		"description": "AI-generated formal proofs for the public domain.",
		"attributes": []map[string]any{
			{"trait_type": "Username", "value": "flow-contributor"},
			{"trait_type": "Conjectures Proved", "value": 1},
			{"trait_type": "Conjectures Attempted", "value": 1},
			{"trait_type": "Cost Donated (USD)", "value": "0.05"},
			{"trait_type": "Proof Status", "value": "complete"},
			{"trait_type": "Proof Mode", "value": "ai"},
		},
	}
	status, resp = postJSON(t, fmt.Sprintf("/contributions/%s/seal", contribID), nft)
	if status != http.StatusCreated {
		t.Fatalf("seal: status %d, body %v", status, resp)
	}
	if _, ok := resp["pr_url"]; !ok {
		t.Error("seal response missing pr_url")
	}

	// 5. Verify the contribution is retrievable (rebuild may be async)
	waitFor(t, 5*time.Second, "contribution appears in GET /contributions", func() bool {
		var contributions []contribution
		getJSON(t, "/contributions", &contributions)
		for _, c := range contributions {
			if c.ContributionID == contribID {
				return true
			}
		}
		return false
	})
	var contributions []contribution
	getJSON(t, "/contributions", &contributions)
	for _, c := range contributions {
		if c.ContributionID == contribID {
			if c.Username != "flow-contributor" {
				t.Errorf("username = %q, want %q", c.Username, "flow-contributor")
			}
			if c.ConjecturesProved != 1 {
				t.Errorf("conjectures_proved = %d, want 1", c.ConjecturesProved)
			}
			if c.Prover != "rocq" {
				t.Errorf("prover = %q, want %q", c.Prover, "rocq")
			}
			break
		}
	}
}

func TestCertifierFlow(t *testing.T) {
	// 1. List available contribution reviews, verify alice's package exists
	var pkgs []struct {
		ContributorContributionID string   `json:"contributor_contribution_id"`
		ContributorUsername       string   `json:"contributor_username"`
		Prover                    string   `json:"prover"`
		ConjectureIDs             []string `json:"conjecture_ids"`
		CertifiedBy               []string `json:"certified_by"`
	}
	getJSON(t, "/contribution-reviews", &pkgs)
	var aliceFound bool
	for _, p := range pkgs {
		if p.ContributorUsername == "alice" {
			aliceFound = true
			break
		}
	}
	if !aliceFound {
		t.Fatal("prerequisite failed: alice's package not found in /contribution-reviews")
	}

	// 2. Create certificate reviewing alice's package
	certID := fmt.Sprintf("flow-cert-%d", time.Now().UnixNano())
	cert := map[string]any{
		"certifier_username":   "flow-certifier",
		"certificate_id":       certID,
		"packages_certified":   1,
		"conjectures_compared": 2,
		"package_rankings": []map[string]any{
			{
				"contributor_contribution_id": "a1111111-1111-1111-1111-111111111111",
				"rank":                        1,
				"overall_score":               95,
			},
		},
		"recommendation": "approved",
	}
	status, resp := postJSON(t, "/certificates", cert)
	if status != http.StatusCreated {
		t.Fatalf("create certificate: status %d, body %v", status, resp)
	}
	if _, ok := resp["commit_sha"]; !ok {
		t.Error("create certificate response missing commit_sha")
	}

	// 3. Seal with NFT metadata
	nft := map[string]any{
		"name":        "Proof@Home Certificate — flow-certifier",
		"description": "Peer-review certificate for contribution packages.",
		"attributes": []map[string]any{
			{"trait_type": "Certifier", "value": "flow-certifier"},
			{"trait_type": "Packages Certified", "value": 1},
			{"trait_type": "Recommendation", "value": "approved"},
		},
	}
	status, resp = postJSON(t, fmt.Sprintf("/certificates/%s/seal", certID), nft)
	if status != http.StatusCreated {
		t.Fatalf("seal certificate: status %d, body %v", status, resp)
	}
	if _, ok := resp["pr_url"]; !ok {
		t.Error("seal certificate response missing pr_url")
	}

	// 4. Verify the certificate appears in the list (rebuild may be async)
	waitFor(t, 5*time.Second, "certificate appears in GET /certificates", func() bool {
		var certs []struct {
			CertificateID string `json:"certificate_id"`
		}
		getJSON(t, "/certificates", &certs)
		for _, c := range certs {
			if c.CertificateID == certID {
				return true
			}
		}
		return false
	})
	var certs []struct {
		CertificateID     string `json:"certificate_id"`
		CertifierUsername string `json:"certifier_username"`
	}
	getJSON(t, "/certificates", &certs)
	for _, c := range certs {
		if c.CertificateID == certID {
			if c.CertifierUsername != "flow-certifier" {
				t.Errorf("certifier_username = %q, want %q", c.CertifierUsername, "flow-certifier")
			}
			break
		}
	}
}

func TestExpositionFlow(t *testing.T) {
	expoID := fmt.Sprintf("test-expo-%d", time.Now().UnixNano())

	// 1. POST /expositions → 201 + commit_sha
	body := map[string]any{
		"exposition_id":   expoID,
		"author_username": "expo-author",
		"contribution_id": "a1111111-1111-1111-1111-111111111111",
		"conjecture_id":   "prob_001_rocq",
		"prover":          "rocq",
		"proof_script":    "Proof. auto. Qed.",
		"exposition_text":  "This proof uses the auto tactic to automatically discharge the goal.",
		"cost_usd":        0.03,
		"strategy_used":   "parse-proof",
	}
	status, resp := postJSON(t, "/expositions", body)
	if status != http.StatusCreated {
		t.Fatalf("POST /expositions: status %d, body %v", status, resp)
	}
	if _, ok := resp["commit_sha"]; !ok {
		t.Error("response missing commit_sha")
	}

	// 2. POST /expositions/{id}/seal → 201 + pr_url
	nft := map[string]any{
		"name":        "Proof@Home Exposition — expo-author",
		"description": "AI-generated proof exposition.",
		"attributes": []map[string]any{
			{"trait_type": "Author Username", "value": "expo-author"},
			{"trait_type": "Exposition ID", "value": expoID},
			{"trait_type": "Conjecture ID", "value": "prob_001_rocq"},
			{"trait_type": "Prover", "value": "rocq"},
			{"trait_type": "AI Cost (USD)", "value": "0.0300"},
			{"trait_type": "Strategy Used", "value": "parse-proof"},
		},
	}
	status, resp = postJSON(t, fmt.Sprintf("/expositions/%s/seal", expoID), nft)
	if status != http.StatusCreated {
		t.Fatalf("POST /expositions/{id}/seal: status %d, body %v", status, resp)
	}
	if _, ok := resp["pr_url"]; !ok {
		t.Error("response missing pr_url")
	}

	// 3. GET /expositions → verify expoID in list (rebuild may be async)
	waitFor(t, 5*time.Second, "exposition appears in GET /expositions", func() bool {
		var expositions []struct {
			ExpositionID string `json:"exposition_id"`
		}
		getJSON(t, "/expositions", &expositions)
		for _, e := range expositions {
			if e.ExpositionID == expoID {
				return true
			}
		}
		return false
	})
	var expositions []struct {
		ExpositionID   string `json:"exposition_id"`
		AuthorUsername string `json:"author_username"`
		ConjectureID   string `json:"conjecture_id"`
		Prover         string `json:"prover"`
		StrategyUsed   string `json:"strategy_used"`
	}
	getJSON(t, "/expositions", &expositions)
	for _, e := range expositions {
		if e.ExpositionID == expoID {
			if e.AuthorUsername != "expo-author" {
				t.Errorf("author_username = %q, want %q", e.AuthorUsername, "expo-author")
			}
			if e.ConjectureID != "prob_001_rocq" {
				t.Errorf("conjecture_id = %q, want %q", e.ConjectureID, "prob_001_rocq")
			}
			if e.Prover != "rocq" {
				t.Errorf("prover = %q, want %q", e.Prover, "rocq")
			}
			break
		}
	}

	// 4. GET /expositions/{id} → verify fields match
	var expo struct {
		ExpositionID   string  `json:"exposition_id"`
		AuthorUsername string  `json:"author_username"`
		ExpositionText string  `json:"exposition_text"`
		CostUSD        float64 `json:"cost_usd"`
		StrategyUsed   string  `json:"strategy_used"`
	}
	getJSON(t, fmt.Sprintf("/expositions/%s", expoID), &expo)
	if expo.ExpositionID != expoID {
		t.Errorf("exposition_id = %q, want %q", expo.ExpositionID, expoID)
	}
	if expo.ExpositionText == "" {
		t.Error("exposition_text is empty")
	}
	if expo.CostUSD != 0.03 {
		t.Errorf("cost_usd = %f, want 0.03", expo.CostUSD)
	}
}

func TestConjectureAuthorFlow(t *testing.T) {
	conjID := fmt.Sprintf("flow_conj_%d", time.Now().UnixNano())
	// 1. Build a tar.gz with one valid conjecture
	conjectures := []map[string]any{
		{
			"id":              conjID,
			"title":           "Flow test conjecture",
			"difficulty":      "easy",
			"prover":          "lean4",
			"status":          "open",
			"preamble":        "import Mathlib.Tactic",
			"lemma_statement": "theorem flow_test : 1 + 1 = 2 := by norm_num",
			"hints":           []string{"try norm_num"},
			"skeleton":        "theorem flow_test : 1 + 1 = 2 := by sorry",
		},
	}
	archive := buildConjectureTarGz(t, conjectures)

	// 2. Submit the tar.gz archive
	status, resp := postRaw(t, "/conjectures", "application/gzip", archive)
	if status != http.StatusOK {
		t.Fatalf("submit conjectures: status %d, body %v", status, resp)
	}
	if resp["status"] != "accepted" {
		t.Errorf("status = %q, want %q", resp["status"], "accepted")
	}
	if count, ok := resp["count"].(float64); !ok || count != 1 {
		t.Errorf("count = %v, want 1", resp["count"])
	}
	batchID, ok := resp["batch_id"].(string)
	if !ok || batchID == "" {
		t.Fatal("response missing batch_id")
	}
	if _, ok := resp["commit_sha"]; !ok {
		t.Error("response missing commit_sha")
	}

	// 3. Seal the conjecture batch with NFT metadata
	nft := map[string]any{
		"name":        "Proof@Home Conjectures — flow batch",
		"description": "New conjectures submitted to the public domain.",
		"attributes": []map[string]any{
			{"trait_type": "Batch ID", "value": batchID},
			{"trait_type": "Conjecture Count", "value": 1},
			{"trait_type": "Proof Assistant", "value": "lean4"},
		},
	}
	status, resp = postJSON(t, fmt.Sprintf("/conjectures/batches/%s/seal", batchID), nft)
	if status != http.StatusOK {
		t.Fatalf("seal conjectures: status %d, body %v", status, resp)
	}
	if resp["status"] != "sealed" {
		t.Errorf("seal status = %q, want %q", resp["status"], "sealed")
	}

	// 4. Verify the new conjecture appears in the list (rebuild may be async)
	waitFor(t, 5*time.Second, "conjecture appears in GET /conjectures", func() bool {
		var conjs []conjecture
		getJSON(t, "/conjectures", &conjs)
		for _, c := range conjs {
			if c.ID == conjID {
				return true
			}
		}
		return false
	})
	var allConjectures []conjecture
	getJSON(t, "/conjectures", &allConjectures)
	for _, c := range allConjectures {
		if c.ID == conjID {
			if c.Title != "Flow test conjecture" {
				t.Errorf("title = %q, want %q", c.Title, "Flow test conjecture")
			}
			if c.Prover != "lean4" {
				t.Errorf("prover = %q, want %q", c.Prover, "lean4")
			}
			break
		}
	}
}

func deleteRequest(t *testing.T, path string) int {
	t.Helper()
	req, err := http.NewRequest("DELETE", serverURL+path, nil)
	if err != nil {
		t.Fatalf("DELETE %s: %v", path, err)
	}
	resp, err := httpClient.Do(req)
	if err != nil {
		t.Fatalf("DELETE %s: %v", path, err)
	}
	defer resp.Body.Close()
	return resp.StatusCode
}

func TestNotesCRUD(t *testing.T) {
	// Use an existing lesson from seed data or create one for the test
	lessonID := "test-lesson-notes"
	// Create a lesson for this test
	lessonBody := map[string]any{
		"lesson_id":       lessonID,
		"author_username": "test-notes-user",
		"title":           "Test Lesson for Notes",
		"topic":           "testing",
		"difficulty":      "easy",
		"conjecture_ids":  []string{},
		"published":       true,
		"content":         "Line 1\nLine 2\nLine 3\n",
	}
	postJSON(t, "/lessons", lessonBody)

	// 1. POST note -> 201
	note := map[string]any{
		"anchor_text":     "Line 2",
		"content":         "This is important!",
		"highlight_color": "yellow",
		"line_start":      2,
		"line_end":        2,
		"content_hash":    "abc123",
		"user_id":         "test-user",
		"username":        "tester",
	}
	status, resp := postJSON(t, fmt.Sprintf("/lessons/%s/notes", lessonID), note)
	if status != http.StatusCreated {
		t.Fatalf("POST note: status %d, body %v", status, resp)
	}
	noteID, ok := resp["note_id"].(string)
	if !ok || noteID == "" {
		t.Fatal("response missing note_id")
	}

	// 2. GET notes -> verify note appears
	var notes []map[string]any
	getJSON(t, fmt.Sprintf("/lessons/%s/notes", lessonID), &notes)
	if len(notes) < 1 {
		t.Fatalf("GET notes: got %d, want >= 1", len(notes))
	}
	var found bool
	for _, n := range notes {
		if n["note_id"] == noteID {
			found = true
			if n["content"] != "This is important!" {
				t.Errorf("content = %q, want %q", n["content"], "This is important!")
			}
			break
		}
	}
	if !found {
		t.Errorf("note %s not found in GET response", noteID)
	}

	// 3. PATCH note -> update content
	patch := map[string]any{
		"content":         "Updated note content",
		"highlight_color": "blue",
	}
	status, resp = patchJSON(t, fmt.Sprintf("/notes/%s", noteID), patch)
	if status != http.StatusOK {
		t.Fatalf("PATCH note: status %d, body %v", status, resp)
	}
	if resp["content"] != "Updated note content" {
		t.Errorf("updated content = %q, want %q", resp["content"], "Updated note content")
	}
	if resp["highlight_color"] != "blue" {
		t.Errorf("updated color = %q, want %q", resp["highlight_color"], "blue")
	}

	// 4. DELETE note -> 204
	status = deleteRequest(t, fmt.Sprintf("/notes/%s", noteID))
	if status != http.StatusNoContent {
		t.Fatalf("DELETE note: status %d, want 204", status)
	}

	// 5. GET notes -> verify empty
	var notesAfter []map[string]any
	getJSON(t, fmt.Sprintf("/lessons/%s/notes", lessonID), &notesAfter)
	for _, n := range notesAfter {
		if n["note_id"] == noteID {
			t.Errorf("note %s still present after DELETE", noteID)
		}
	}
}

// ── Credits / Edition flow ──

func TestLessonCreditsFlow(t *testing.T) {
	lessonID := fmt.Sprintf("test-credits-%d", time.Now().UnixNano())

	// 1. POST /lessons → creates lesson with auto-generated CREDITS.toml
	status, resp := postJSON(t, "/lessons", map[string]any{
		"lesson_id":       lessonID,
		"author_username": "alice",
		"title":           "Test Credits Lesson",
		"conjecture_ids":  []string{},
		"published":       true,
	})
	if status != http.StatusCreated && status != http.StatusOK {
		t.Fatalf("POST /lessons: status %d, body %v", status, resp)
	}
	if sha, ok := resp["commit_sha"].(string); !ok || sha == "" {
		t.Errorf("expected non-empty commit_sha, got %v", resp["commit_sha"])
	}

	// 2. GET /lessons/{id} → verify credits field present
	waitFor(t, 5*time.Second, "lesson with credits appears", func() bool {
		var lesson map[string]any
		body := get(t, fmt.Sprintf("/lessons/%s", lessonID))
		json.Unmarshal(body, &lesson)
		_, hasCredits := lesson["credits"]
		return hasCredits && lesson["credits"] != nil
	})

	// Verify credits structure
	var lesson map[string]any
	getJSON(t, fmt.Sprintf("/lessons/%s", lessonID), &lesson)
	credits, ok := lesson["credits"].(map[string]any)
	if !ok {
		t.Fatalf("credits is not a map: %T", lesson["credits"])
	}

	contributors, ok := credits["contributors"].([]any)
	if !ok || len(contributors) == 0 {
		t.Fatalf("expected non-empty contributors, got %v", credits["contributors"])
	}
	first := contributors[0].(map[string]any)
	if first["username"] != "alice" {
		t.Errorf("first contributor = %q, want alice", first["username"])
	}
	if first["role"] != "author" {
		t.Errorf("first contributor role = %q, want author", first["role"])
	}

	edition, ok := credits["edition"].(map[string]any)
	if !ok {
		t.Fatalf("edition is not a map: %T", credits["edition"])
	}
	if edition["current"] != float64(1) {
		t.Errorf("edition.current = %v, want 1", edition["current"])
	}

	// 3. PATCH /lessons/{id} as "bob" → verify bob added as contributor
	patchJSON(t, fmt.Sprintf("/lessons/%s", lessonID), map[string]any{
		"author_username": "bob",
		"title":           "Test Credits Lesson (updated)",
	})

	// Wait for rebuild and check contributors
	waitFor(t, 5*time.Second, "bob appears as contributor", func() bool {
		var l map[string]any
		body := get(t, fmt.Sprintf("/lessons/%s", lessonID))
		json.Unmarshal(body, &l)
		c, ok := l["credits"].(map[string]any)
		if !ok {
			return false
		}
		contribs, ok := c["contributors"].([]any)
		if !ok {
			return false
		}
		for _, entry := range contribs {
			e := entry.(map[string]any)
			if e["username"] == "bob" {
				return true
			}
		}
		return false
	})

	// 4. POST /lessons/{id}/edition-bump → verify edition incremented
	status, resp = postJSON(t, fmt.Sprintf("/lessons/%s/edition-bump", lessonID), map[string]any{
		"summary": "Added exercises",
	})
	if status != http.StatusOK {
		t.Fatalf("POST edition-bump: status %d, body %v", status, resp)
	}
	if resp["status"] != "bumped" {
		t.Errorf("status = %q, want bumped", resp["status"])
	}

	// Verify edition bumped
	waitFor(t, 5*time.Second, "edition bumped to 2", func() bool {
		var l map[string]any
		body := get(t, fmt.Sprintf("/lessons/%s", lessonID))
		json.Unmarshal(body, &l)
		c, ok := l["credits"].(map[string]any)
		if !ok {
			return false
		}
		ed, ok := c["edition"].(map[string]any)
		if !ok {
			return false
		}
		return ed["current"] == float64(2)
	})
}

func TestEditionBumpMissingSummary(t *testing.T) {
	// edition-bump without summary should fail
	status, resp := postJSON(t, "/lessons/nonexistent/edition-bump", map[string]any{})
	if status != http.StatusBadRequest {
		t.Errorf("expected 400 for missing summary, got %d: %v", status, resp)
	}
}

func TestSeriesCreditsFlow(t *testing.T) {
	seriesID := fmt.Sprintf("test-credits-series-%d", time.Now().UnixNano())

	// 1. POST /series → creates series with auto-generated CREDITS.toml
	status, resp := postJSON(t, "/series", map[string]any{
		"series_id":       seriesID,
		"title":           "Test Credits Series",
		"author_username": "carol",
		"lesson_ids":      []string{},
		"published":       true,
	})
	if status != http.StatusCreated && status != http.StatusOK {
		t.Fatalf("POST /series: status %d, body %v", status, resp)
	}

	// 2. GET /series/{id} → verify credits
	waitFor(t, 5*time.Second, "series with credits appears", func() bool {
		var s map[string]any
		body := get(t, fmt.Sprintf("/series/%s", seriesID))
		json.Unmarshal(body, &s)
		_, hasCredits := s["credits"]
		return hasCredits && s["credits"] != nil
	})

	// 3. POST /series/{id}/edition-bump
	status, resp = postJSON(t, fmt.Sprintf("/series/%s/edition-bump", seriesID), map[string]any{
		"summary": "Added module 5",
	})
	if status != http.StatusOK {
		t.Fatalf("POST series edition-bump: status %d, body %v", status, resp)
	}
}
