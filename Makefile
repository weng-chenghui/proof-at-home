.PHONY: build build-client build-server build-pocketbase clean run-server run-pocketbase run-init run-donate run-prove run-status test conjectures help

# Paths
CLIENT_BIN = target/release/proof-at-home
CLIENT_DEBUG = target/debug/proof-at-home

help: ## Show this help
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'

# ── Build ──────────────────────────────────────────────

build: build-client build-server build-pocketbase ## Build everything (release)

build-client: ## Build Rust CLI (release)
	cargo build --release

build-server: ## Build Go server
	go build -o target/proof-at-home-server ./src/server

build-pocketbase: ## Build PocketBase server
	go build -o pah-pocketbase ./cmd/pocketbase

build-debug: ## Build Rust CLI (debug, faster compile)
	cargo build

# ── Run ────────────────────────────────────────────────

run-server: build-server ## Start the conjecture server
	CONJECTURES_DIR=conjectures ./target/proof-at-home-server

run-pocketbase: build-pocketbase ## Start the PocketBase server
	CONJECTURES_DIR=./conjectures ./pah-pocketbase serve

run-login: build-debug ## Log in with auth token from web UI
	$(CLIENT_DEBUG) login

run-setup: build-debug ## Configure CLI settings
	$(CLIENT_DEBUG) setup

run-init: build-debug ## Run setup wizard (deprecated)
	$(CLIENT_DEBUG) init

run-donate: build-debug ## Set donation budget
	$(CLIENT_DEBUG) donate

run-prove: build-debug ## Start a proof contribution
	$(CLIENT_DEBUG) prove

run-status: build-debug ## Show config and stats
	$(CLIENT_DEBUG) status

# ── Test ───────────────────────────────────────────────

test: test-client test-server ## Run all tests

test-client: ## Run Rust tests
	cargo test

test-server: ## Run Go tests
	go test ./src/server/...

check: ## Cargo check (fast type-checking, no codegen)
	cargo check

lint: ## Run clippy + go vet
	cargo clippy -- -D warnings
	go vet ./src/server/...

# ── Utilities ──────────────────────────────────────────

clean: ## Remove build artifacts
	cargo clean
	rm -f target/proof-at-home-server pah-pocketbase

health: ## Ping the server health endpoint
	@curl -sf http://localhost:8080/health && echo "" || echo "Server not running"

conjectures: ## List conjectures from the server
	@curl -sf http://localhost:8080/conjectures | python3 -m json.tool || echo "Server not running"

fmt: ## Format Rust and Go code
	cargo fmt
	gofmt -w src/server/
