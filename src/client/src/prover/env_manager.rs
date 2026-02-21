use anyhow::{bail, Context, Result};
use sha2::{Digest, Sha256};
use std::path::PathBuf;
use std::process::Command;

use crate::server_client::api::{CoqDeps, Dependencies, LeanDeps, Problem};

/// A fully resolved proof environment ready for compilation.
#[derive(Debug, Clone)]
pub struct ResolvedEnv {
    pub project_dir: PathBuf,
    pub theories_dir: PathBuf,
    pub build_cmd: Vec<String>,
    pub opam_switch: Option<String>,
}

/// Manages virtual project environments for proof compilation.
pub struct EnvManager {
    envs_root: PathBuf,
}

impl EnvManager {
    pub fn new(envs_dir: &str) -> Self {
        Self {
            envs_root: PathBuf::from(envs_dir),
        }
    }

    /// Ensure the environment for a problem is set up and ready.
    /// Returns a ResolvedEnv with paths and build commands.
    pub fn ensure_env(&self, problem: &Problem) -> Result<ResolvedEnv> {
        let deps = problem
            .dependencies
            .as_ref()
            .context("Problem is missing dependencies field")?;

        match deps {
            Dependencies::Coq(coq_deps) => self.ensure_coq_env(coq_deps),
            Dependencies::Lean(lean_deps) => self.ensure_lean_env(lean_deps),
        }
    }

    /// Compute a short hash for dependency grouping.
    fn dep_hash(canonical: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(canonical.as_bytes());
        let result = hasher.finalize();
        hex::encode(&result[..4]) // 8 hex chars
    }

    /// Build a canonical JSON string for Coq dependencies (for hashing).
    fn coq_canonical(deps: &CoqDeps) -> String {
        let mut packages = deps.opam_packages.clone();
        packages.sort();
        serde_json::json!({
            "coq_version": deps.coq_version,
            "opam_packages": packages,
        })
        .to_string()
    }

    /// Build a canonical JSON string for Lean dependencies (for hashing).
    fn lean_canonical(deps: &LeanDeps) -> String {
        let mut packages = deps.lake_packages.clone();
        packages.sort();
        serde_json::json!({
            "lean_toolchain": deps.lean_toolchain,
            "lake_packages": packages,
        })
        .to_string()
    }

    fn ensure_coq_env(&self, deps: &CoqDeps) -> Result<ResolvedEnv> {
        let canonical = Self::coq_canonical(deps);
        let hash = Self::dep_hash(&canonical);
        let env_name = format!("coq-{}-{}", deps.coq_version, hash);
        let env_dir = self.envs_root.join("coq").join(&env_name);
        let theories_dir = env_dir.join("theories");
        let ready_marker = env_dir.join(".ready");
        let switch_name = format!("proof-at-home-{}", hash);

        if ready_marker.exists() {
            return Ok(ResolvedEnv {
                project_dir: env_dir,
                theories_dir,
                build_cmd: vec![
                    "opam".into(),
                    "exec".into(),
                    format!("--switch={}", switch_name),
                    "--".into(),
                    "dune".into(),
                    "build".into(),
                ],
                opam_switch: Some(switch_name),
            });
        }

        std::fs::create_dir_all(&theories_dir)?;

        // Step a: create opam switch
        eprintln!("  Creating opam switch '{}'...", switch_name);
        let status = Command::new("opam")
            .args([
                "switch",
                "create",
                &switch_name,
                "ocaml-base-compiler.5.2.1",
            ])
            .status()
            .context("Failed to run opam switch create")?;
        if !status.success() {
            // Switch might already exist, try to use it
            let check = Command::new("opam")
                .args(["switch", "show", "--switch", &switch_name])
                .output();
            if check.map(|o| o.status.success()).unwrap_or(false) {
                eprintln!("  Switch '{}' already exists, reusing.", switch_name);
            } else {
                bail!("Failed to create opam switch '{}'", switch_name);
            }
        }

        // Step b: install coq and packages
        let coq_pkg = format!("coq.{}", deps.coq_version);
        let mut install_args = vec![
            "install".to_string(),
            "-y".to_string(),
            format!("--switch={}", switch_name),
            coq_pkg,
            "dune".to_string(),
        ];
        for pkg in &deps.opam_packages {
            install_args.push(pkg.clone());
        }
        eprintln!("  Installing Coq packages (this may take a while)...");
        let status = Command::new("opam")
            .args(&install_args)
            .status()
            .context("Failed to run opam install")?;
        if !status.success() {
            bail!("opam install failed for switch '{}'", switch_name);
        }

        // Step c: generate project files
        // _CoqProject
        std::fs::write(env_dir.join("_CoqProject"), "-R theories PaH\n")?;

        // dune-project
        std::fs::write(
            env_dir.join("dune-project"),
            "(lang dune 3.16)\n(using coq 0.8)\n",
        )?;

        // theories/dune
        std::fs::write(theories_dir.join("dune"), "(coq.theory\n (name PaH))\n")?;

        // Generate Dockerfile and Makefile for reproducible verification
        std::fs::write(
            env_dir.join("Dockerfile"),
            Self::generate_dockerfile_coq(deps),
        )?;
        std::fs::write(
            env_dir.join("Makefile"),
            Self::generate_makefile("coq", &env_name, &switch_name),
        )?;

        // Step d: touch .ready
        std::fs::write(&ready_marker, "")?;

        Ok(ResolvedEnv {
            project_dir: env_dir,
            theories_dir,
            build_cmd: vec![
                "opam".into(),
                "exec".into(),
                format!("--switch={}", switch_name),
                "--".into(),
                "dune".into(),
                "build".into(),
            ],
            opam_switch: Some(switch_name),
        })
    }

    fn ensure_lean_env(&self, deps: &LeanDeps) -> Result<ResolvedEnv> {
        let canonical = Self::lean_canonical(deps);
        let hash = Self::dep_hash(&canonical);
        let toolchain_version = deps
            .lean_toolchain
            .rsplit(':')
            .next()
            .unwrap_or(&deps.lean_toolchain);
        let env_name = format!("lean-{}-{}", toolchain_version, hash);
        let env_dir = self.envs_root.join("lean").join(&env_name);
        let pah_dir = env_dir.join("PaH");
        let ready_marker = env_dir.join(".ready");

        if ready_marker.exists() {
            return Ok(ResolvedEnv {
                project_dir: env_dir,
                theories_dir: pah_dir,
                build_cmd: vec!["lake".into(), "build".into()],
                opam_switch: None,
            });
        }

        std::fs::create_dir_all(&env_dir)?;

        // Step a: write lean-toolchain
        std::fs::write(env_dir.join("lean-toolchain"), &deps.lean_toolchain)?;

        // Step b: lake init
        let has_mathlib = deps.lake_packages.iter().any(|p| p == "mathlib");
        eprintln!("  Initializing Lean project...");
        let mut init_args = vec!["init".to_string(), "PaH".to_string()];
        if has_mathlib {
            init_args.push("math".to_string());
        }
        let status = Command::new("lake")
            .current_dir(&env_dir)
            .args(&init_args)
            .status()
            .context("Failed to run lake init")?;
        if !status.success() {
            bail!("lake init failed");
        }

        // Step c: download pre-built Mathlib oleans if using Mathlib
        if has_mathlib {
            eprintln!("  Downloading Mathlib cache (this may take a while)...");
            let status = Command::new("lake")
                .current_dir(&env_dir)
                .args(["exe", "cache", "get"])
                .status()
                .context("Failed to run lake exe cache get")?;
            if !status.success() {
                eprintln!("  Warning: lake exe cache get failed, will build from source");
            }
        }

        // Step d: lake build
        eprintln!("  Building Lean project...");
        let status = Command::new("lake")
            .current_dir(&env_dir)
            .args(["build"])
            .status()
            .context("Failed to run lake build")?;
        if !status.success() {
            bail!("lake build failed");
        }

        // Ensure PaH directory exists
        std::fs::create_dir_all(&pah_dir)?;

        // Generate Dockerfile and Makefile for reproducible verification
        std::fs::write(
            env_dir.join("Dockerfile"),
            Self::generate_dockerfile_lean(deps),
        )?;
        std::fs::write(
            env_dir.join("Makefile"),
            Self::generate_makefile("lean", &env_name, ""),
        )?;

        // Step e: touch .ready
        std::fs::write(&ready_marker, "")?;

        Ok(ResolvedEnv {
            project_dir: env_dir,
            theories_dir: pah_dir,
            build_cmd: vec!["lake".into(), "build".into()],
            opam_switch: None,
        })
    }

    fn generate_dockerfile_coq(deps: &CoqDeps) -> String {
        let coq_pkg = format!("coq.{}", deps.coq_version);
        let mut opam_pkgs = vec![coq_pkg, "dune".to_string()];
        opam_pkgs.extend(deps.opam_packages.iter().cloned());
        let opam_install_list = opam_pkgs.join(" ");

        format!(
            r#"# Stage 1: Install Coq + dependencies via opam
FROM ocaml/opam:debian-12-ocaml-5.2 AS builder
RUN opam update && opam install -y {opam_install_list}

# Stage 2: Slim runtime with just the opam switch copied in
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends make && rm -rf /var/lib/apt/lists/*
COPY --from=builder /home/opam/.opam/default /opt/opam
ENV PATH="/opt/opam/bin:$PATH"
ENV COQLIB="/opt/opam/lib/coq"
WORKDIR /workspace
COPY _CoqProject dune-project ./
COPY theories/ theories/
CMD ["dune", "build"]
"#
        )
    }

    fn generate_dockerfile_lean(deps: &LeanDeps) -> String {
        let toolchain = &deps.lean_toolchain;

        format!(
            r#"# Stage 1: Install elan + lean + lake, build dependencies
FROM ubuntu:24.04 AS builder
RUN apt-get update && apt-get install -y curl git && rm -rf /var/lib/apt/lists/*
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain {toolchain}
ENV PATH="/root/.elan/bin:$PATH"
WORKDIR /workspace
COPY lakefile.lean lean-toolchain ./
COPY lakefile.toml ./
RUN lake build

# Stage 2: Slim runtime
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends git && rm -rf /var/lib/apt/lists/*
COPY --from=builder /root/.elan /root/.elan
ENV PATH="/root/.elan/bin:$PATH"
WORKDIR /workspace
COPY --from=builder /workspace .
COPY PaH/ PaH/
CMD ["lake", "build"]
"#
        )
    }

    fn generate_makefile(prover: &str, env_name: &str, switch_name: &str) -> String {
        let build_cmd = match prover {
            "coq" => format!("opam exec --switch={} -- dune build", switch_name),
            _ => "lake build".to_string(),
        };

        format!(
            r#".PHONY: build docker-build docker-run

build:
	{build_cmd}

docker-build:
	docker build -t pah-{env_name} .

docker-run: docker-build
	docker run --rm pah-{env_name}
"#
        )
    }
}
