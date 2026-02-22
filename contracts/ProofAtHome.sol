// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Proof@Home NFT Contract
//
// A minimal ERC-721 contract for minting proof-of-contribution NFTs.
// Each token represents a verified proof session or review, with metadata
// stored on IPFS.
//
// Deployment:
//   1. Install OpenZeppelin: npm install @openzeppelin/contracts
//   2. Compile: solc --optimize --bin --abi contracts/ProofAtHome.sol
//      Or with Foundry: forge build
//      Or with Hardhat: npx hardhat compile
//   3. Deploy to an L2 (Base, Arbitrum, or Optimism recommended for low gas)
//
// Minting flow:
//   1. Run `proof-at-home publish session <id>` to get token URI
//   2. Call `mint(recipientAddress, tokenURI)` on the deployed contract

import "@openzeppelin/contracts/token/ERC721/extensions/ERC721URIStorage.sol";
import "@openzeppelin/contracts/access/Ownable.sol";

contract ProofAtHome is ERC721URIStorage, Ownable {
    uint256 private _nextTokenId;

    constructor() ERC721("ProofAtHome", "PROOF") Ownable(msg.sender) {}

    /// Mint a new NFT with the given IPFS token URI. Owner-only.
    function mint(address to, string memory tokenURI) external onlyOwner returns (uint256) {
        uint256 tokenId = _nextTokenId++;
        _mint(to, tokenId);
        _setTokenURI(tokenId, tokenURI);
        return tokenId;
    }
}
