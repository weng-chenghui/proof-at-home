# Proof@Home NFT Publishing Guide

End-to-end guide for publishing proof-of-contribution NFTs on-chain.

**What the NFT represents:** The NFT is not about ownership — proofs are CC0 public domain. The NFT records *who funded and verified* the work, like a donor's name on a university building. It is a permanent, verifiable receipt of your contribution to the corpus of formally verified mathematics.

## Overview

The publishing flow has three stages:

```
proof-at-home prove        →  local proof archive + NFT metadata
proof-at-home publish      →  IPFS-pinned archive + mint-ready script
./mint.sh                  →  on-chain ERC-721 NFT
```

Each stage produces artifacts in the contribution directory (`~/.proof-at-home/contributions/<id>/`).

---

## Prerequisites

### 1. Foundry (for on-chain minting)

Foundry provides `cast`, the CLI tool used to send transactions.

```bash
curl -L https://foundry.paradigm.xyz | bash
foundryup
```

Verify: `cast --version`

### 2. IPFS Pinning Service

NFT metadata and archives are stored on IPFS. You need a pinning service account:

- **[Pinata](https://www.pinata.cloud/)** — free tier: 500 pins, 1 GB
- **[nft.storage](https://nft.storage/)** — free, backed by Filecoin
- **Local IPFS node** — `ipfs daemon` on localhost:5001

### 3. Ethereum Wallet

You need an Ethereum-compatible wallet with:
- A **deployer key** (private key for the contract owner)
- A **recipient address** (wallet that will own the NFTs)
- Enough ETH/gas on your chosen network

### 4. RPC Endpoint

An Ethereum RPC URL for your target network:
- **[Alchemy](https://www.alchemy.com/)** — free tier available
- **[Infura](https://www.infura.io/)** — free tier available
- Local node (Anvil for testing: `anvil`)

### Recommended Networks

| Network  | Type     | Gas Cost | Notes                        |
|----------|----------|----------|------------------------------|
| Base     | L2       | ~$0.01   | Coinbase L2, recommended     |
| Arbitrum | L2       | ~$0.01   | Ethereum rollup              |
| Optimism | L2       | ~$0.01   | Ethereum rollup              |
| Sepolia  | Testnet  | Free     | Use for testing              |
| Mainnet  | L1       | ~$5-50   | Only if you need L1 security |

**Total publishing cost:** IPFS pinning is free (Pinata free tier: 500 pins, 1 GB). On-chain minting costs ~$0.01 on L2 networks. The only ongoing cost is gas for minting.

---

## Step-by-Step

### Step 1: Configure IPFS

Add your pinning service credentials to `~/.proof-at-home/config.toml`:

```toml
[ipfs]
api_url = "https://api.pinata.cloud"
api_key = "your-pinata-jwt-token"
```

**Getting a Pinata JWT:**
1. Sign up at [pinata.cloud](https://www.pinata.cloud/)
2. Go to API Keys → New Key
3. Enable "pinFileToIPFS" and "pinJSONToIPFS" permissions
4. Copy the JWT token

### Step 2: Run a Proof Contribution

```bash
proof-at-home prove
```

This creates:
- `~/.proof-at-home/contributions/<contribution-id>/proofs.tar.gz` — proof archive
- `~/.proof-at-home/contributions/<contribution-id>/nft_metadata.json` — NFT metadata

Note the contribution ID from the output.

### Step 3: Publish to IPFS

```bash
proof-at-home publish contribution <contribution-id>
```

This:
1. Pins the proof archive to IPFS
2. Updates NFT metadata with the archive's IPFS CID
3. Pins the metadata to IPFS
4. Generates `mint_ready.json` with CIDs and token URI
5. Generates `mint.sh` — a ready-to-run minting script

Output files in the contribution directory:
```
mint_ready.json              # CIDs and token URI
mint.sh                      # Executable minting script
nft_metadata_published.json  # Final metadata with IPFS links
```

For reviews, use:
```bash
proof-at-home publish review <review-id>
```

### Step 4: Deploy the Contract (one-time)

Deploy the `ProofAtHome.sol` contract to your chosen network:

```bash
cd contracts

# Install OpenZeppelin (if using Foundry)
forge install OpenZeppelin/openzeppelin-contracts

# Deploy
forge create ProofAtHome.sol:ProofAtHome \
  --rpc-url $RPC_URL \
  --private-key $DEPLOYER_KEY
```

Save the deployed contract address. You only need to do this once — all NFTs are minted on the same contract.

### Step 5: Mint the NFT

Set the required environment variables:

```bash
export CONTRACT_ADDRESS="0x..."       # From step 4
export RECIPIENT="0x..."              # Wallet to receive the NFT
export RPC_URL="https://..."          # Your RPC endpoint
export DEPLOYER_KEY="0x..."           # Contract owner's private key
```

Then run the generated script:

```bash
cd ~/.proof-at-home/contributions/<contribution-id>
./mint.sh
```

The script calls `cast send` to mint the NFT with the IPFS-hosted metadata.

---

## Verifying Your NFT

After minting:

1. **Block explorer** — search for the transaction hash on [Basescan](https://basescan.org/), [Arbiscan](https://arbiscan.io/), etc.
2. **OpenSea** — your NFT should appear automatically (may take a few minutes to index)
3. **Metadata** — view the raw metadata at `https://ipfs.io/ipfs/<metadata-cid>`
4. **Archive** — download the proof archive at `https://ipfs.io/ipfs/<archive-cid>`

### Verifying the Signature

The NFT metadata includes an ed25519 signature over the archive hash. To verify:

```python
# Python example using ed25519
from nacl.signing import VerifyKey
import binascii

public_key_hex = "..."    # From NFT "Public Key" attribute
signature_hex = "..."     # From NFT "Archive Signature" attribute
archive_sha256 = "..."    # From NFT "Archive SHA-256" attribute

verify_key = VerifyKey(binascii.unhexlify(public_key_hex))
verify_key.verify(
    binascii.unhexlify(archive_sha256),
    binascii.unhexlify(signature_hex)
)
print("Signature valid")
```

---

## File Reference

After publishing, the contribution directory contains:

| File                        | Created by      | Description                          |
|-----------------------------|-----------------|--------------------------------------|
| `proofs.tar.gz`             | `prove`         | Proof archive                        |
| `nft_metadata.json`         | `prove`         | Original NFT metadata (local)        |
| `nft_metadata_published.json` | `publish`     | Final metadata with IPFS CIDs        |
| `mint_ready.json`           | `publish`       | CIDs and token URI for minting       |
| `mint.sh`                   | `publish`       | Executable minting script            |

---

## Troubleshooting

### "IPFS not configured"

Add the `[ipfs]` section to `~/.proof-at-home/config.toml`. See Step 1.

### "No signing key found"

Run `proof-at-home init` to generate an ed25519 keypair. The public key is stored in config; the private key is at `~/.proof-at-home/signing_key.hex`.

### IPFS pinning fails

- Check your API key is valid and has pinning permissions
- Check the file size — free tiers have limits (typically 100 MB per file)
- For local IPFS, ensure `ipfs daemon` is running on port 5001

### `cast` command not found

Install Foundry: `curl -L https://foundry.paradigm.xyz | bash && foundryup`

### Transaction reverts

- Ensure `DEPLOYER_KEY` is the contract owner (the address that deployed it)
- Ensure the wallet has enough ETH for gas
- Check the RPC URL matches your target network

---

## Testing Locally

Use Foundry's `anvil` for a local testnet:

```bash
# Terminal 1: start local chain
anvil

# Terminal 2: deploy and mint
export RPC_URL="http://localhost:8545"
export DEPLOYER_KEY="0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80"  # anvil default key
export CONTRACT_ADDRESS=$(forge create contracts/ProofAtHome.sol:ProofAtHome \
  --rpc-url $RPC_URL --private-key $DEPLOYER_KEY --json | jq -r '.deployedTo')
export RECIPIENT="0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266"  # anvil default address

./mint.sh
```
