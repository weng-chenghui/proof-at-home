.PHONY: build build-client build-server clean run-server run-init run-donate run run-status test help

# Paths
CLIENT_BIN = target/release/proof-at-home
CLIENT_DEBUG = target/debug/proof-at-home

help: ## Show this help
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | sort | awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-20s\033[0m %s\n", $$1, $$2}'

# ── Build ──────────────────────────────────────────────

build: build-client build-server ## Build everything (release)

build-client: ## Build Rust CLI (release)
	cargo build --release

build-server: ## Build Go server
	go build -o target/proof-at-home-server ./src/server

build-debug: ## Build Rust CLI (debug, faster compile)
	cargo build

# ── Run ────────────────────────────────────────────────

run-server: build-server ## Start the problem server
	PROBLEMS_DIR=problems ./target/proof-at-home-server

run-init: build-debug ## Run setup wizard
	$(CLIENT_DEBUG) init

run-donate: build-debug ## Set donation budget
	$(CLIENT_DEBUG) donate

run: build-debug ## Start a proof session
	$(CLIENT_DEBUG) run

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
	rm -f target/proof-at-home-server

health: ## Ping the server health endpoint
	@curl -sf http://localhost:8080/health && echo "" || echo "Server not running"

problems: ## List problems from the server
	@curl -sf http://localhost:8080/problems | python3 -m json.tool || echo "Server not running"

fmt: ## Format Rust and Go code
	cargo fmt
	gofmt -w src/server/
