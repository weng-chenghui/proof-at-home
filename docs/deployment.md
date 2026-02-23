# Deployment Guide

## Quick Start (Recommended): PocketBase on Fly.io

The fastest way to get proof-at-home running publicly. PocketBase is an open-source backend that packs a database (SQLite), authentication, file storage, and an admin dashboard into a single executable. Fly.io hosts it with persistent storage for free.

### 1. Build

```bash
go build -o pah-pocketbase ./cmd/pocketbase
```

This compiles PocketBase with the proof-at-home API routes, web UI, database migrations, and business logic hooks into a single binary.

### 2. Try It Locally

```bash
CONJECTURES_DIR=./conjectures ./pah-pocketbase serve
```

On first run, PocketBase automatically:
- Creates `pb_data/` with a SQLite database and local file storage
- Runs migrations to create the `conjectures`, `contribution_results`, `contributions`, and `certificates` collections
- Seeds conjectures from the `CONJECTURES_DIR` directory

Open `http://127.0.0.1:8090/` for the web UI, `http://127.0.0.1:8090/_/` for the admin dashboard.

### 3. Deploy to Fly.io

Install the Fly CLI if you haven't: `curl -L https://fly.io/install.sh | sh`

**Create `fly.toml` in the project root:**

```toml
app = "proof-at-home"
primary_region = "nrt"  # Tokyo; change to your nearest region

[build]
  dockerfile = "Dockerfile.pocketbase"

[env]
  CONJECTURES_DIR = "/conjectures"

[http_service]
  internal_port = 8090
  force_https = true

[[mounts]]
  source = "pb_data"
  destination = "/app/pb_data"
```

**Deploy:**

```bash
# Sign up / log in
fly auth login

# Launch the app (first time only)
fly launch --copy-config --no-deploy

# Create a persistent volume for SQLite data
fly volumes create pb_data --size 1 --region nrt

# Deploy
fly deploy
```

Your app is now live at `https://proof-at-home.fly.dev/`.

**After deployment:**

1. Visit `https://proof-at-home.fly.dev/_/` to create the admin account
2. Visit `https://proof-at-home.fly.dev/` to use the web UI

**Useful Fly commands:**

```bash
fly logs              # View live logs
fly ssh console       # SSH into the running container
fly status            # Check app status
fly scale count 1     # Ensure single instance (SQLite needs this)
```

### 4. Set Up the Admin Dashboard

Open `/_/` on your deployment. On the first visit, you'll be prompted to create a Superuser email and password. The admin dashboard lets you:

- Browse and edit all collections (conjectures, contribution_results, contributions, certificates)
- Manage users and authentication settings
- Configure file storage (local or S3-compatible)
- View logs and create backups

### 5. Enable OAuth Providers (Optional)

To let users log in via GitHub, Google, or Facebook on the web UI's `/login.html` page:

1. Go to `/_/` > **Settings** > **Auth providers**
2. Enable the providers you want (GitHub, Google, Facebook)
3. For each provider, paste the **Client ID** and **Client Secret** from the provider's developer console:
   - **GitHub**: [github.com/settings/developers](https://github.com/settings/developers) — create an OAuth App, set the callback URL to `https://your-domain.com/api/oauth2-redirect`
   - **Google**: [console.cloud.google.com](https://console.cloud.google.com/) — Credentials > OAuth 2.0 Client IDs, set authorized redirect URI to `https://your-domain.com/api/oauth2-redirect`
   - **Facebook**: [developers.facebook.com](https://developers.facebook.com/) — create an app, add Facebook Login product, set Valid OAuth Redirect URI to `https://your-domain.com/api/oauth2-redirect`
4. Save. Users can now sign in from the Login page.

### 6. What You Get

Everything runs from the single binary — no Postgres, no Redis, no separate file server:

| Feature | Details |
|---|---|
| Database | SQLite, zero configuration |
| Web UI | Embedded at `/` (conjecture browser, submission forms, certificate dashboard) |
| Admin UI | Built-in at `/_/` (data browser, user management, logs, backups) |
| API | 9 backward-compatible endpoints (same as custom server) |
| Auth | Built-in password, OAuth2, OTP |
| File storage | Local by default, S3-compatible optional |
| CRUD API | Auto-generated at `/api/collections/{name}/records` with filtering, sorting, pagination |
| Realtime | SSE subscriptions for live updates |

### Custom Port

```bash
./pah-pocketbase serve --http=0.0.0.0:8080
```

### Business Logic Hooks

Two hooks run automatically (defined in `cmd/pocketbase/hooks/hooks.go`):

1. **Auto-prove**: When a `contribution_results` record is created with `success=true`, the corresponding conjecture's status is set to `"proved"`.
2. **Certificate tracking**: When a `certificates` record is created, the `certified_by` field on affected contributions is updated with the certifier's username.

### Optional: GCP Cloud Storage

By default, file uploads (proof archives) are stored locally in `pb_data/storage/`. To use GCP Cloud Storage instead, configure via the admin UI at Settings > Files storage, or via environment variables:

```bash
PB_S3_BUCKET=proof-archives \
PB_S3_REGION=auto \
PB_S3_ENDPOINT=https://storage.googleapis.com \
PB_S3_ACCESS_KEY=GOOG1E... \
PB_S3_SECRET=... \
./pah-pocketbase serve
```

To generate HMAC keys, go to Cloud Console > Cloud Storage > Settings > Interoperability > Create a key for a service account.

### Alternative Remote: Bare VM

If you prefer a VPS (Hetzner, DigitalOcean, etc.) over Fly.io:

```bash
# Build and copy to server
CGO_ENABLED=0 GOOS=linux go build -o pah-pocketbase ./cmd/pocketbase
scp pah-pocketbase conjectures/ user@server:~/pah/
```

Create `/etc/systemd/system/pah-pocketbase.service`:

```ini
[Unit]
Description=proof-at-home PocketBase
After=network.target

[Service]
ExecStart=/home/user/pah/pah-pocketbase serve --http=0.0.0.0:8090
WorkingDirectory=/home/user/pah
Environment=CONJECTURES_DIR=/home/user/pah/conjectures
Restart=always

[Install]
WantedBy=multi-user.target
```

```bash
sudo systemctl enable --now pah-pocketbase
```

For HTTPS, put Caddy in front (auto-provisions Let's Encrypt certs):

```
pah.example.com {
    reverse_proxy localhost:8090
}
```

### Alternative Remote: GCP Cloud Run

```bash
# Build and push container
gcloud auth configure-docker
docker build -f Dockerfile.pocketbase -t gcr.io/PROJECT_ID/pah-pocketbase .
docker push gcr.io/PROJECT_ID/pah-pocketbase

# Deploy (single instance for SQLite consistency)
gcloud run deploy pah-pocketbase \
  --image gcr.io/PROJECT_ID/pah-pocketbase \
  --region us-central1 \
  --allow-unauthenticated \
  --port 8090 \
  --cpu 1 --memory 512Mi \
  --min-instances 1 \
  --max-instances 1 \
  --set-env-vars "CONJECTURES_DIR=/conjectures" \
  --execution-environment gen2 \
  --add-volume name=pb-data,type=cloud-storage,bucket=pah-pb-data \
  --add-volume-mount volume=pb-data,mount-path=/pb_data
```

Notes:
- `--min-instances 1` keeps the instance warm (SQLite needs a persistent process)
- `--max-instances 1` prevents concurrent writes to SQLite
- The volume mount stores `pb_data/` in a GCS bucket so data survives redeployments

---

## Web UI

Both deployment options embed a web frontend served from the root URL. No separate static hosting is needed — everything is compiled into the single binary via `go:embed`.

| Page | Path | Description |
|---|---|---|
| Landing | `/` | Navigation cards linking to all sections |
| Conjectures | `/conjectures.html` | Filterable conjecture list (difficulty, prover) |
| Conjecture Detail | `/conjecture.html?id=xxx` | Code blocks for preamble, lemma, skeleton, hints |
| Certificates | `/certificates.html` | Certificate packages with archive download links |
| Submit Conjecture | `/submit-conjecture.html` | Upload tar.gz or provide git URL |
| Submit Result | `/submit-result.html` | Single proof result form |
| Submit Contribution | `/submit-batch.html` | Proof contribution form |
| Submit Certificate | `/submit-certificate.html` | Certificate form with dynamic package rankings |
| Login | `/login.html` | OAuth login (GitHub, Google, Facebook) for PocketBase deployments |
| Settings | `/settings.html` | JWT token configuration (stored in browser localStorage) |

The web UI uses vanilla JS with Alpine.js (CDN) for dynamic forms. Auth tokens configured in Settings are sent as `Bearer` headers on all API requests.

---

## API Endpoints

Both deployment options serve identical endpoints:

| Method | Path | Description |
|---|---|---|
| `GET` | `/health` | Health check |
| `GET` | `/conjectures` | List all conjectures |
| `GET` | `/conjectures/{id}` | Get a specific conjecture |
| `POST` | `/conjectures/packages` | Submit conjectures (tar.gz or JSON) |
| `POST` | `/contributions` | Submit a proof result |
| `POST` | `/contributions/batch` | Submit a contribution summary |
| `GET` | `/certificate-packages` | List certificate packages |
| `GET` | `/certificate-packages/{contributionID}/archive` | Download proof archive |
| `POST` | `/certificates` | Submit a certificate |

When `AUTH_ENABLED=true` (custom server) or using PocketBase auth, POST endpoints require authentication. GET endpoints are always public.

---

## Alternative: Custom Server

If you need PostgreSQL, custom JWT auth (Auth0/Firebase), or full control over the server code, you can use the custom Go server instead of PocketBase.

### Minimal (in-memory, no persistence)

```bash
go build -o server ./src/server
./server
```

Conjectures are loaded from `./conjectures/` by default. Data is lost on restart.

Open `http://localhost:8080/` to access the web UI for browsing conjectures, submitting proofs, and reviewing packages.

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
| `CONJECTURES_DIR` | `conjectures` | Directory containing conjecture JSON files |
| `SEED_CERTIFICATIONS` | (empty) | Directory containing seed contribution JSON files |
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

## Quick Reference

| | PocketBase (Recommended) | Custom Server |
|---|---|---|
| Entry point | `go run ./cmd/pocketbase serve` | `go run ./src/server` |
| Database | SQLite (built-in) | Memory, SQLite, or PostgreSQL |
| File storage | Local or S3 | Local or S3 |
| Auth | Built-in (password, OAuth2, OTP) | Auth0/Firebase JWT (optional) |
| Web UI | `http://localhost:8090/` | `http://localhost:8080/` |
| Admin UI | `http://localhost:8090/_/` | None |
| Remote hosting | Fly.io (recommended), Cloud Run, VPS | Docker Compose, VPS |

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
    conjectures.html               Conjecture browser
    conjecture.html                Conjecture detail
    certificates.html              Certificate dashboard
    submit-*.html                  Submission forms (conjecture, contribution, batch, certificate)
    login.html                     OAuth login (PocketBase deployments)
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
  handlers/                        HTTP handlers (conjectures, contributions, certificates, packages, health)

cmd/pocketbase/                    PocketBase deployment
  main.go                          PocketBase entry point + backward-compatible routes + web UI
  migrations/001_collections.go    Collection schema definitions
  hooks/hooks.go                   Business logic (auto-prove, certificate tracking)

Dockerfile                         Multi-stage build for custom server
Dockerfile.pocketbase              Multi-stage build for PocketBase
fly.toml                           Fly.io deployment config
docker-compose.yml                 Custom server + Postgres + MinIO
```
