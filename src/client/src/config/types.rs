use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Config {
    pub identity: Identity,
    pub api: Api,
    pub prover: Prover,
    pub budget: Budget,
    #[serde(default)]
    pub ipfs: Ipfs,
    #[serde(default)]
    pub pool: Pool,
    #[serde(default = "default_registries")]
    pub registries: Vec<RegistryConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryConfig {
    pub name: String,
    pub url: String,
}

fn default_registries() -> Vec<RegistryConfig> {
    vec![RegistryConfig {
        name: "official".to_string(),
        url: "github:proof-at-home/proof-at-home".to_string(),
    }]
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Pool {
    #[serde(default)]
    pub dir: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Ipfs {
    #[serde(default)]
    pub api_url: String,
    #[serde(default)]
    pub api_key: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Identity {
    #[serde(default)]
    pub real_name: String,
    #[serde(default)]
    pub username: String,
    #[serde(default)]
    pub email: String,
    #[serde(default)]
    pub affiliation: String,
    #[serde(default)]
    pub public_key: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Api {
    /// AI provider: "anthropic", "openai", or "ollama"
    #[serde(default = "default_provider")]
    pub provider: String,
    /// Provider API key (replaces the old anthropic_api_key)
    #[serde(default, alias = "anthropic_api_key")]
    pub api_key: String,
    /// Override the provider's base URL (for Azure, self-hosted, etc.)
    #[serde(default)]
    pub api_base_url: String,
    #[serde(default)]
    pub server_url: String,
    #[serde(default = "default_model")]
    pub model: String,
    #[serde(default)]
    pub auth_token: String,
}

impl Default for Api {
    fn default() -> Self {
        Self {
            provider: default_provider(),
            api_key: String::new(),
            api_base_url: String::new(),
            server_url: String::new(),
            model: default_model(),
            auth_token: String::new(),
        }
    }
}

fn default_provider() -> String {
    "anthropic".to_string()
}

fn default_model() -> String {
    "claude-sonnet-4-6".to_string()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Prover {
    #[serde(default = "default_scratch_dir")]
    pub scratch_dir: String,
    #[serde(default = "default_envs_dir")]
    pub envs_dir: String,
}

impl Default for Prover {
    fn default() -> Self {
        Self {
            scratch_dir: default_scratch_dir(),
            envs_dir: default_envs_dir(),
        }
    }
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
    pub run_spent: f64,
    #[serde(default)]
    pub total_spent: f64,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            donated_usd: 0.0,
            run_spent: 0.0,
            total_spent: 0.0,
        }
    }
}

impl Config {
    pub fn load_or_default() -> Self {
        Self::load().unwrap_or_default()
    }

    /// Effective provider name (env var override > config).
    pub fn provider(&self) -> String {
        std::env::var("PAH_PROVIDER").unwrap_or_else(|_| {
            if self.api.provider.is_empty() {
                "anthropic".to_string()
            } else {
                self.api.provider.clone()
            }
        })
    }

    /// Effective API key (env var override > config).
    pub fn api_key(&self) -> String {
        std::env::var("PAH_API_KEY").unwrap_or_else(|_| self.api.api_key.clone())
    }

    /// Effective API base URL (env var override > config).
    pub fn api_base_url(&self) -> String {
        std::env::var("PAH_API_BASE_URL").unwrap_or_else(|_| self.api.api_base_url.clone())
    }

    /// Effective model name (env var override > config).
    pub fn model(&self) -> String {
        std::env::var("PAH_MODEL").unwrap_or_else(|_| {
            if self.api.model.is_empty() {
                default_model()
            } else {
                self.api.model.clone()
            }
        })
    }

    /// Budget in USD for agent runs. Uses donated_usd if set, otherwise defaults to 5.0.
    pub fn budget_usd(&self) -> f64 {
        if self.budget.donated_usd > 0.0 {
            self.budget.donated_usd
        } else {
            5.0
        }
    }

    pub fn server_url(&self) -> String {
        std::env::var("PAH_SERVER_URL").unwrap_or_else(|_| {
            if self.api.server_url.is_empty() {
                "http://localhost:8080".to_string()
            } else {
                self.api.server_url.clone()
            }
        })
    }

    pub fn require_login(&self) -> Result<()> {
        if self.api.auth_token.is_empty() {
            println!("\nWelcome to Proof@Home!\n");
            println!("To get started, run:  pah auth login\n");
            std::process::exit(0);
        }
        Ok(())
    }

    pub fn config_dir() -> Result<PathBuf> {
        let home = dirs::home_dir().context("Could not determine home directory")?;
        Ok(home.join(".proof-at-home"))
    }

    pub fn config_path() -> Result<PathBuf> {
        Ok(Self::config_dir()?.join("config.toml"))
    }

    pub fn pool_dir(&self) -> Result<PathBuf> {
        if !self.pool.dir.is_empty() {
            Ok(PathBuf::from(&self.pool.dir))
        } else {
            Ok(Self::config_dir()?.join("pool"))
        }
    }

    pub fn contributions_dir() -> Result<PathBuf> {
        Ok(Self::config_dir()?.join("contributions"))
    }

    pub fn signing_key_path() -> Result<PathBuf> {
        Ok(Self::config_dir()?.join("signing_key.hex"))
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
}
