use anyhow::{Context, Result};
use ed25519_dalek::{Signer, SigningKey, VerifyingKey};
use rand::rngs::OsRng;

/// Generate a new ed25519 keypair. Returns (private_key_hex, public_key_hex).
pub fn generate_keypair() -> (String, String) {
    let signing_key = SigningKey::generate(&mut OsRng);
    let verifying_key: VerifyingKey = signing_key.verifying_key();

    let private_hex = hex::encode(signing_key.to_bytes());
    let public_hex = hex::encode(verifying_key.to_bytes());

    (private_hex, public_hex)
}

/// Load a signing key from a hex-encoded 32-byte seed.
pub fn load_signing_key(hex_str: &str) -> Result<SigningKey> {
    let bytes = hex::decode(hex_str.trim()).context("Invalid hex in signing key")?;
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| anyhow::anyhow!("Signing key must be exactly 32 bytes"))?;
    Ok(SigningKey::from_bytes(&bytes))
}

/// Sign a git commit SHA (given as hex string) with ed25519. Returns the signature as hex.
pub fn sign_commit(key: &SigningKey, commit_sha_hex: &str) -> Result<String> {
    let hash_bytes = hex::decode(commit_sha_hex.trim()).context("Invalid hex in commit SHA")?;
    let signature = key.sign(&hash_bytes);
    Ok(hex::encode(signature.to_bytes()))
}
