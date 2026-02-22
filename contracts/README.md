# Proof@Home NFT Contract

Minimal ERC-721 contract for minting proof-of-contribution NFTs.

## Prerequisites

- [Foundry](https://book.getfoundry.sh/getting-started/installation) or [Hardhat](https://hardhat.org/)
- OpenZeppelin Contracts v5

## Compilation

### With Foundry

```bash
forge install OpenZeppelin/openzeppelin-contracts
forge build
```

### With Hardhat

```bash
npm install @openzeppelin/contracts
npx hardhat compile
```

## Deployment

Deploy to an Ethereum L2 for low gas costs:

- **Base** — Coinbase L2, low fees
- **Arbitrum** — Ethereum rollup
- **Optimism** — Ethereum rollup

Example with Foundry:

```bash
forge create contracts/ProofAtHome.sol:ProofAtHome \
  --rpc-url $RPC_URL \
  --private-key $DEPLOYER_KEY
```

## Minting Flow

1. Run a proof session: `proof-at-home run`
2. Publish to IPFS: `proof-at-home publish session <session-id>`
3. Note the token URI from the output
4. Call `mint(recipientAddress, tokenURI)` on the deployed contract

```bash
cast send $CONTRACT_ADDRESS \
  "mint(address,string)" \
  $RECIPIENT \
  "ipfs://QmMetadataCID" \
  --rpc-url $RPC_URL \
  --private-key $OWNER_KEY
```
