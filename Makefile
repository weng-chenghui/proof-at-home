.PHONY: build build-client build-server build-pocketbase clean run-server run-pocketbase run-init run-donate run-prove run-status test test-integration test-integration-pocketbase conjectures help dev-setup dev-run dev-clean dev-reset setup-github setup-gitlab test-docker test-docker-install test-docker-tools test-docker-require

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

build-pocketbase: ## Build PocketBase server
	go build -o target/pah-pocketbase ./cmd/pocketbase

build-debug: ## Build Rust CLI (debug, faster compile)
	cargo build

# ── Run ────────────────────────────────────────────────

run-server: build-server ## Start the conjecture server
	CONJECTURES_DIR=conjectures ./target/proof-at-home-server

run-pocketbase: build-pocketbase dev-setup ## Run PocketBase with local dev environment
	GIT_DATA_REPO_URL=.dev/data-repo.git \
	GIT_DATA_REPO_PATH=.dev/data \
	GIT_FORGE_TYPE=local \
	CONJECTURES_DIR=conjectures \
	./target/pah-pocketbase serve --http=0.0.0.0:8090

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

# ── Dev ───────────────────────────────────────────────

dev-setup: ## Create local dev environment with example data
	@./scripts/dev-setup.sh

dev-run: ## Build and run server with local dev environment
	@./scripts/dev-run.sh

dev-clean: ## Remove local dev state (.dev/)
	rm -rf .dev/
	@echo "Dev environment cleaned. Run 'make dev-setup' to recreate."

dev-reset: dev-clean dev-setup ## Clean and recreate dev environment

setup-github: ## Create data repo on GitHub (usage: make setup-github SERVER_URL=https://...)
	@./scripts/setup-github.sh $(SERVER_URL)

setup-gitlab: ## Create data repo on GitLab (usage: make setup-gitlab SERVER_URL=https://...)
	@./scripts/setup-gitlab.sh $(SERVER_URL)

# ── Test ───────────────────────────────────────────────

test: test-client test-server ## Run all tests

test-client: ## Run Rust tests
	cargo test

test-server: ## Run Go tests
	go test ./src/server/...

test-integration: ## Run integration tests (requires running server)
	go test -v -count=1 ./tests/integration/...

test-integration-pocketbase: ## Run integration tests against PocketBase server
	TEST_SERVER_URL=http://localhost:8090 go test -v -count=1 ./tests/integration/...

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

conjectures: ## List conjectures from the server
	@curl -sf http://localhost:8080/conjectures | python3 -m json.tool || echo "Server not running"

fmt: ## Format Rust and Go code
	cargo fmt
	gofmt -w src/server/

# ── Docker Tests ──────────────────────────────────────

PAH_LINUX_BIN = .build/pah

$(PAH_LINUX_BIN): ## Build Linux pah binary via Docker (for macOS hosts)
	@mkdir -p .build
	docker run --rm \
	  -v $(CURDIR):/workspace -w /workspace \
	  rust:1-bookworm \
	  cargo build --release
	cp target/release/pah $(PAH_LINUX_BIN)

build-linux: $(PAH_LINUX_BIN) ## Build Linux pah binary via Docker

test-docker-install: $(PAH_LINUX_BIN) ## Run install.sh tests in Docker
	docker build -f tests/docker/Dockerfile.install-sh \
	  --build-arg PAH_BINARY=$(PAH_LINUX_BIN) -t pah-test-install .
	docker run --rm pah-test-install

test-docker-tools: $(PAH_LINUX_BIN) ## Run pah tools tests in Docker
	docker build -f tests/docker/Dockerfile.tools \
	  --build-arg PAH_BINARY=$(PAH_LINUX_BIN) -t pah-test-tools .
	docker run --rm pah-test-tools

test-docker-require: $(PAH_LINUX_BIN) ## Run require_tool error tests in Docker
	docker build -f tests/docker/Dockerfile.require-tool \
	  --build-arg PAH_BINARY=$(PAH_LINUX_BIN) -t pah-test-require .
	docker run --rm pah-test-require

test-docker: test-docker-install test-docker-tools test-docker-require ## Run all Docker tests
