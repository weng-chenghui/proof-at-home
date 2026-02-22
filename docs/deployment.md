# Deployment Guide

The proof-at-home server can be deployed in two ways: the **custom Go server** or **PocketBase**. Both expose the same 9 API endpoints, the same web UI, and accept the same JSON payloads, so the existing client (`proof-at-home run`) works against either one.

## Quick Reference

| | Custom Server | PocketBase |
|---|---|---|
| Entry point | `go run ./src/server` | `go run ./cmd/pocketbase serve` |
| Database | Memory, SQLite, or PostgreSQL | SQLite (built-in) |
| File storage | Local or S3 | Local or S3 |
| Auth | Auth0/Firebase JWT (optional) | Built-in (password, OAuth2, OTP) |
| Web UI | `http://localhost:8080/` | `http://localhost:8090/` |
| Admin UI | None | `http://localhost:8090/_/` |
| Best for | Production with Postgres, full control | Quick setup, single binary, admin UI |

---

## Option A: Custom Server

### Minimal (in-memory, no persistence)

```bash
go build -o server ./src/server
./server
```

Problems are loaded from `./problems/` by default. Data is lost on restart.

Open `http://localhost:8080/` to access the web UI for browsing problems, submitting proofs, and reviewing packages.

### SQLite (lightweight persistence)

```bash
STORE_BACKEND=sqlite DATABASE_PATH=./data.db ./server
```

### PostgreSQL

```bash
STORE_BACKEND=postgres DATABASE_URL=postgres://user:pass@localhost:5432/proofathome?sslmode=disable ./server
```

Migrations run automatically on startup.

### Docker Compose (Postgres + MinIO + server)

```bash
docker compose up --build
```

This starts three services:

- **server** on port 8080 (Postgres backend, S3 storage)
- **postgres** on port 5432
- **minio** on ports 9000 (API) / 9001 (console)

### Environment Variables

| Variable | Default | Description |
|---|---|---|
| `PORT` | `8080` | HTTP listen port |
| `PROBLEMS_DIR` | `problems` | Directory containing problem JSON files |
| `SEED_REVIEWS` | (empty) | Directory containing seed session JSON files |
| `STORE_BACKEND` | `memory` | `memory`, `sqlite`, or `postgres` |
| `DATABASE_URL` | (empty) | PostgreSQL connection string |
| `DATABASE_PATH` | `proofathome.db` | SQLite file path |
| `S3_ENDPOINT` | (empty) | S3-compatible endpoint (e.g., `minio:9000`) |
| `S3_BUCKET` | (empty) | S3 bucket name |
| `S3_REGION` | `us-east-1` | S3 region |
| `S3_ACCESS_KEY` | (empty) | S3 access key |
| `S3_SECRET_KEY` | (empty) | S3 secret key |
| `S3_USE_SSL` | `true` | Set `false` for MinIO over HTTP |
| `AUTH_ENABLED` | `false` | Enable JWT auth on POST endpoints |
| `AUTH_ISSUER` | (empty) | JWT issuer URL (e.g., `https://your-tenant.auth0.com/`) |
| `AUTH_AUDIENCE` | (empty) | JWT audience |
| `CORS_ORIGINS` | `*` | Comma-separated allowed origins |
| `LOG_LEVEL` | `info` | `debug`, `info`, `warn`, or `error` |

### Health Check

```bash
curl http://localhost:8080/health
# {"status":"ok","checks":{"database":"ok","storage":"ok"}}
```

Returns HTTP 503 if any check fails.

---

## Option B: PocketBase

### Quick Start

```bash
go build -o pah-pocketbase ./cmd/pocketbase
./pah-pocketbase serve
```

On first run, PocketBase creates `pb_data/` (SQLite database + local file storage) and runs migrations to create the `problems`, `proof_results`, `sessions`, and `reviews` collections.

Open `http://localhost:8090/` to access the web UI. Visit `http://localhost:8090/_/` to set up the admin account.

### With GCP Cloud Storage

GCP Cloud Storage provides an S3-compatible XML API. Configure via the admin UI at Settings > Files storage, or via environment variables:

```bash
PB_S3_BUCKET=proof-archives \
PB_S3_REGION=auto \
PB_S3_ENDPOINT=https://storage.googleapis.com \
PB_S3_ACCESS_KEY=GOOG1E... \
PB_S3_SECRET=... \
./pah-pocketbase serve
```

To generate HMAC keys for GCP, go to Cloud Console > Cloud Storage > Settings > Interoperability > Create a key for a service account.

### Custom Port

```bash
./pah-pocketbase serve --http=0.0.0.0:8080
```

### Seeding Problems

Set `PROBLEMS_DIR` to load problem JSON files on startup:

```bash
PROBLEMS_DIR=./problems ./pah-pocketbase serve
```

### Deploy to GCP Cloud Run

Cloud Run runs the PocketBase container as a serverless service. SQLite data is stored on a persistent volume.

**1. Build and push the container image:**

```bash
gcloud auth configure-docker
docker build -f Dockerfile.pocketbase -t gcr.io/PROJECT_ID/pah-pocketbase .
docker push gcr.io/PROJECT_ID/pah-pocketbase
```

**2. Deploy with a persistent volume for SQLite data:**

```bash
gcloud run deploy pah-pocketbase \
  --image gcr.io/PROJECT_ID/pah-pocketbase \
  --region us-central1 \
  --allow-unauthenticated \
  --port 8090 \
  --cpu 1 --memory 512Mi \
  --min-instances 1 \
  --max-instances 1 \
  --set-env-vars "PROBLEMS_DIR=/problems" \
  --set-env-vars "PB_S3_BUCKET=proof-archives" \
  --set-env-vars "PB_S3_REGION=auto" \
  --set-env-vars "PB_S3_ENDPOINT=https://storage.googleapis.com" \
  --set-env-vars "PB_S3_ACCESS_KEY=GOOG1E..." \
  --set-env-vars "PB_S3_SECRET=..." \
  --execution-environment gen2 \
  --add-volume name=pb-data,type=cloud-storage,bucket=pah-pb-data \
  --add-volume-mount volume=pb-data,mount-path=/pb_data
```

Notes:
- `--min-instances 1` keeps the instance warm (PocketBase uses SQLite, which needs a persistent process)
- `--max-instances 1` prevents concurrent writes to SQLite
- The volume mount stores `pb_data/` in a GCS bucket so data survives redeployments
- File uploads (proof archives) go to the separate GCS bucket configured via `PB_S3_*` env vars

**3. Set up the admin account:**

After deployment, visit `https://pah-pocketbase-xxxxx.run.app/_/` to create the first admin account.

### Deploy to a VPS (Fly.io, Railway, or bare VM)

**Fly.io:**

```bash
# fly.toml
fly launch --image gcr.io/PROJECT_ID/pah-pocketbase
fly volumes create pb_data --size 1
fly deploy
```

**Bare VM (systemd):**

```bash
# Build locally
CGO_ENABLED=0 GOOS=linux go build -o pah-pocketbase ./cmd/pocketbase
scp pah-pocketbase problems/ user@server:~/pah/

# On the server, create /etc/systemd/system/pah-pocketbase.service
[Unit]
Description=proof-at-home PocketBase
After=network.target

[Service]
ExecStart=/home/user/pah/pah-pocketbase serve --http=0.0.0.0:8090
WorkingDirectory=/home/user/pah
Environment=PROBLEMS_DIR=/home/user/pah/problems
Restart=always

[Install]
WantedBy=multi-user.target
```

```bash
sudo systemctl enable --now pah-pocketbase
```

Put nginx or Caddy in front for HTTPS. Caddy example:

```
pah.example.com {
    reverse_proxy localhost:8090
}
```

### What PocketBase Provides

In addition to the 9 backward-compatible API endpoints and the embedded web UI, PocketBase auto-generates:

- Full CRUD at `/api/collections/{name}/records` with filtering, sorting, pagination
- Auth endpoints at `/api/collections/users/auth-with-password`, OAuth2, OTP
- File upload/download per record
- Realtime subscriptions (SSE) for live updates
- Backup and restore via admin UI
- Logs viewer in admin UI

### Business Logic

Two hooks run automatically (defined in `cmd/pocketbase/hooks/hooks.go`):

1. **Auto-prove**: When a `proof_results` record is created with `success=true`, the corresponding problem's status is set to `"proved"`.
2. **Review tracking**: When a `reviews` record is created, the `reviewed_by` field on affected sessions is updated with the reviewer's username.

---

## Web UI

Both deployment options embed a web frontend served from the root URL. No separate static hosting is needed — everything is compiled into the single binary via `go:embed`.

| Page | Path | Description |
|---|---|---|
| Landing | `/` | Navigation cards linking to all sections |
| Problems | `/problems.html` | Filterable problem list (difficulty, proof assistant) |
| Problem Detail | `/problem.html?id=xxx` | Code blocks for preamble, lemma, skeleton, hints |
| Reviews | `/reviews.html` | Review packages with archive download links |
| Submit Problem | `/submit-problem.html` | Upload tar.gz or provide git URL |
| Submit Result | `/submit-result.html` | Single proof result form |
| Submit Batch | `/submit-batch.html` | Session summary form |
| Submit Review | `/submit-review.html` | Review form with dynamic package rankings |
| Settings | `/settings.html` | JWT token configuration (stored in browser localStorage) |

The web UI uses vanilla JS with Alpine.js (CDN) for dynamic forms. Auth tokens configured in Settings are sent as `Bearer` headers on all API requests.

---

## API Endpoints

Both deployment options serve identical endpoints:

| Method | Path | Description |
|---|---|---|
| `GET` | `/health` | Health check |
| `GET` | `/problems` | List all problems |
| `GET` | `/problems/{id}` | Get a specific problem |
| `POST` | `/problems/packages` | Submit problems (tar.gz or JSON) |
| `POST` | `/results` | Submit a proof result |
| `POST` | `/results/batch` | Submit a session summary |
| `GET` | `/review-packages` | List review packages |
| `GET` | `/review-packages/{sessionID}/archive` | Download proof archive |
| `POST` | `/reviews` | Submit a review |

When `AUTH_ENABLED=true` (custom server) or using PocketBase auth, POST endpoints require authentication. GET endpoints are always public.

---

## Architecture

```
src/server/                        Custom Go server
  main.go                          Entry point (chi router, graceful shutdown)
  config/config.go                 Env var configuration
  logging/logging.go               Structured JSON logging (slog)
  data/schema.go                   Shared data types
  static/                          Embedded web UI (shared by both deployments)
    embed.go                       Exports embedded FS as static.Files
    index.html                     Landing page
    problems.html                  Problem browser
    problem.html                   Problem detail
    reviews.html                   Review dashboard
    submit-*.html                  Submission forms (problem, result, batch, review)
    settings.html                  JWT token configuration
    shared.css                     Shared stylesheet
    shared.js                      API helper + nav bar injection
  store/
    store.go                       Store interface (repository pattern)
    memory.go                      In-memory implementation
    sqlite/sqlite.go               SQLite implementation (modernc.org/sqlite, no CGO)
    postgres/postgres.go           PostgreSQL implementation (lib/pq)
  storage/
    storage.go                     ObjectStorage interface
    s3.go                          S3-compatible implementation (minio-go)
    local.go                       Local filesystem fallback
  middleware/auth.go               JWT auth (JWKS, Auth0/Firebase)
  handlers/                        HTTP handlers (problems, results, reviews, packages, health)

cmd/pocketbase/                    PocketBase deployment
  main.go                          PocketBase entry point + backward-compatible routes + web UI
  migrations/001_collections.go    Collection schema definitions
  hooks/hooks.go                   Business logic (auto-prove, review tracking)

Dockerfile                         Multi-stage build for custom server
Dockerfile.pocketbase              Multi-stage build for PocketBase
docker-compose.yml                 Server + Postgres + MinIO
```
