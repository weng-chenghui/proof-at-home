use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    pub identity: Identity,
    pub api: Api,
    pub proof_assistant: ProofAssistant,
    pub budget: Budget,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Identity {
    pub real_name: String,
    pub username: String,
    pub email: String,
    #[serde(default)]
    pub affiliation: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Api {
    pub anthropic_api_key: String,
    pub server_url: String,
    #[serde(default = "default_model")]
    pub model: String,
}

fn default_model() -> String {
    "claude-sonnet-4-6".to_string()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofAssistant {
    #[serde(default = "default_scratch_dir")]
    pub scratch_dir: String,
    #[serde(default = "default_envs_dir")]
    pub envs_dir: String,
}

fn default_scratch_dir() -> String {
    "/tmp/proof-at-home".to_string()
}

fn default_envs_dir() -> String {
    let home = dirs::home_dir().unwrap_or_else(|| PathBuf::from("."));
    home.join(".proof-at-home")
        .join("envs")
        .to_string_lossy()
        .to_string()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Budget {
    #[serde(default)]
    pub donated_usd: f64,
    #[serde(default)]
    pub session_spent: f64,
    #[serde(default)]
    pub total_spent: f64,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            donated_usd: 0.0,
            session_spent: 0.0,
            total_spent: 0.0,
        }
    }
}

impl Config {
    pub fn config_dir() -> Result<PathBuf> {
        let home = dirs::home_dir().context("Could not determine home directory")?;
        Ok(home.join(".proof-at-home"))
    }

    pub fn config_path() -> Result<PathBuf> {
        Ok(Self::config_dir()?.join("config.toml"))
    }

    pub fn sessions_dir() -> Result<PathBuf> {
        Ok(Self::config_dir()?.join("sessions"))
    }

    pub fn load() -> Result<Self> {
        let path = Self::config_path()?;
        let content = fs::read_to_string(&path)
            .with_context(|| format!("Could not read config at {}", path.display()))?;
        let config: Config = toml::from_str(&content).context("Failed to parse config.toml")?;
        Ok(config)
    }

    pub fn save(&self) -> Result<()> {
        let dir = Self::config_dir()?;
        fs::create_dir_all(&dir)?;
        let path = Self::config_path()?;
        let content = toml::to_string_pretty(self).context("Failed to serialize config")?;
        fs::write(&path, content)?;
        Ok(())
    }

    pub fn exists() -> bool {
        Self::config_path().map(|p| p.exists()).unwrap_or(false)
    }
}
