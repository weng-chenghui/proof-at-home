# Collaboration Model

## Overview

Proof@Home uses a **git-based async collaboration model**. The data repository is the shared pool. Users clone it locally, browse others' work, fix or improve proofs and conjectures, seal their own version (individual NFT), and push back.

## Key principle: individual sealing

Each contributor gets their own NFT. When Bob improves Alice's proof, Bob seals a new contribution — he does not modify Alice's sealed NFT. Bob's NFT includes a "Based On" attribute that links to Alice's original contribution, creating a provenance chain.

## Commands reference

| Command | Description |
|---------|-------------|
| `pah pool clone [--dir <path>]` | Clone the shared data repo to `~/.proof-at-home/pool/` (or custom dir) |
| `pah pool pull` | Fetch and rebase on `origin/main` |
| `pah pool push` | Push your changes to the remote |
| `pah pool status` | Show git status of the pool directory |

### `pah pool clone`

1. Fetches the data repo git URL from the server (`GET /api/pool-url`)
2. Clones to `~/.proof-at-home/pool/` (or `--dir <path>`)
3. Auto-configures `git config user.name` and `user.email` from your `config.toml` identity
4. If the pool directory already exists, prints a message suggesting `pah pool pull`

### `pah pool pull`

1. Runs `git fetch origin` + `git rebase origin/main`
2. On conflict: prints helpful message with `git rebase --continue` / `--abort` instructions

### `pah pool push`

1. Runs `git push origin HEAD`
2. On auth failure: suggests `pah auth status`

### `pah pool status`

1. Runs `git status` in the pool directory
2. Shows branch, ahead/behind, uncommitted changes

## Workflow example

```
Alice (prover)                         Bob (collaborator)
    |                                       |
    | pah contribution run                  |
    | pah contribution seal <id>            |
    | → Alice's NFT sealed                  |
    |                                       |
    |                                  pah pool clone
    |                                  pah pool pull
    |                                       |
    |                                  # browse pool/contributions/
    |                                  # fix Alice's proof
    |                                       |
    |                                  pah proof submit <conj> fix.v
    |                                  pah contribution seal <bob-id>
    |                                  → Bob's NFT (Based On: Alice)
    |                                       |
    |                                  pah pool push
    |                                       |
    | pah pool pull                         |
    | # sees Bob's improvement              |
```

## What pah helps with

- **Text-based artifacts** — proofs (`.v`, `.lean`), conjectures (JSON), expositions
- **Git sync** — clone, pull, push the shared pool with one command
- **Identity auto-config** — `git user.name` and `user.email` set from your Proof@Home identity
- **NFT sealing with provenance** — your work is credited, with a "Based On" link to the original

## What pah does NOT help with

- **Merge conflicts** — if a rebase conflicts, use standard git commands (`git rebase --continue` / `--abort`). The CLI prints guidance but does not resolve conflicts for you.
- **Video, images, or binaries** — the pool is for text artifacts. Host media on YouTube, IPFS, etc.
- **Real-time editing** — collaboration is async via git. There is no live co-editing.
- **Modifying others' sealed NFTs** — sealed contributions are immutable. You create your own version instead.
