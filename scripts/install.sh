#!/bin/sh
# Proof@Home installer — downloads pre-built pah binary and optionally
# bootstraps prover toolchains (elan, opam).
#
# Usage:
#   curl -fsSL https://pah.fly.dev/install.sh | sh
#   curl -fsSL https://pah.fly.dev/install.sh | sh -s -- --with-lean
#   curl -fsSL https://pah.fly.dev/install.sh | sh -s -- --with-all
#
# Environment variables:
#   PAH_INSTALL   — override install directory (default: ~/.pah)
#   PAH_VERSION   — override version tag (default: latest)

set -eu

GITHUB_REPO="pah-org/proof-at-home"
INSTALL_DIR="${PAH_INSTALL:-$HOME/.pah}"
BIN_DIR="$INSTALL_DIR/bin"

# Flags
WITH_LEAN=0
WITH_ROCQ=0
MINIMAL=0
VERSION="${PAH_VERSION:-}"

# ── Parse arguments ──

while [ $# -gt 0 ]; do
  case "$1" in
    --with-lean)  WITH_LEAN=1 ;;
    --with-rocq)  WITH_ROCQ=1 ;;
    --with-all)   WITH_LEAN=1; WITH_ROCQ=1 ;;
    --minimal)    MINIMAL=1 ;;
    --version)    shift; VERSION="$1" ;;
    --version=*)  VERSION="${1#--version=}" ;;
    *)            echo "Unknown option: $1"; exit 1 ;;
  esac
  shift
done

# ── Helpers ──

info() {
  printf '  %s\n' "$@"
}

success() {
  printf '  \033[32m✓\033[0m %s\n' "$@"
}

error() {
  printf '  \033[31m✗\033[0m %s\n' "$@" >&2
}

command_exists() {
  command -v "$1" >/dev/null 2>&1
}

# ── Phase 1: Install pah binary ──

detect_platform() {
  OS="$(uname -s)"
  ARCH="$(uname -m)"

  case "$OS" in
    Darwin) OS_NAME="darwin" ;;
    Linux)  OS_NAME="linux" ;;
    *)      error "Unsupported OS: $OS"; exit 1 ;;
  esac

  case "$ARCH" in
    x86_64)  ARCH_NAME="amd64" ;;
    aarch64) ARCH_NAME="arm64" ;;
    arm64)   ARCH_NAME="arm64" ;;
    *)       error "Unsupported architecture: $ARCH"; exit 1 ;;
  esac

  TARGET="${OS_NAME}-${ARCH_NAME}"
}

fetch_version() {
  if [ -n "$VERSION" ]; then
    return
  fi

  if command_exists curl; then
    VERSION=$(curl -fsSL "https://api.github.com/repos/${GITHUB_REPO}/releases/latest" | \
      grep '"tag_name"' | sed -E 's/.*"tag_name": *"([^"]+)".*/\1/')
  elif command_exists wget; then
    VERSION=$(wget -qO- "https://api.github.com/repos/${GITHUB_REPO}/releases/latest" | \
      grep '"tag_name"' | sed -E 's/.*"tag_name": *"([^"]+)".*/\1/')
  else
    error "Neither curl nor wget found. Please install one."
    exit 1
  fi

  if [ -z "$VERSION" ]; then
    error "Could not determine latest version from GitHub API."
    error "Try specifying a version: --version v0.1.0"
    exit 1
  fi
}

download_binary() {
  ARCHIVE="pah-${TARGET}.tar.gz"
  URL="https://github.com/${GITHUB_REPO}/releases/download/${VERSION}/${ARCHIVE}"

  echo ""
  echo "Installing Proof@Home CLI ${VERSION} (${TARGET})..."
  echo ""

  mkdir -p "$BIN_DIR"

  TMPDIR_DL="$(mktemp -d)"
  trap 'rm -rf "$TMPDIR_DL"' EXIT

  info "Downloading ${URL}..."
  if command_exists curl; then
    curl -fsSL "$URL" -o "$TMPDIR_DL/$ARCHIVE"
  elif command_exists wget; then
    wget -q "$URL" -O "$TMPDIR_DL/$ARCHIVE"
  fi

  info "Extracting to ${BIN_DIR}/pah..."
  tar xzf "$TMPDIR_DL/$ARCHIVE" -C "$BIN_DIR"
  chmod +x "$BIN_DIR/pah"

  success "pah installed to ${BIN_DIR}/pah"
}

setup_path() {
  EXPORT_LINE="export PATH=\"${BIN_DIR}:\$PATH\""

  # Check common shell config files
  for rc in "$HOME/.zshrc" "$HOME/.bashrc" "$HOME/.profile"; do
    if [ -f "$rc" ]; then
      if grep -qF "$BIN_DIR" "$rc" 2>/dev/null; then
        return  # Already in PATH config
      fi
    fi
  done

  # Determine which rc file to update
  SHELL_NAME="$(basename "${SHELL:-/bin/sh}")"
  case "$SHELL_NAME" in
    zsh)  RC_FILE="$HOME/.zshrc" ;;
    bash) RC_FILE="$HOME/.bashrc" ;;
    *)    RC_FILE="$HOME/.profile" ;;
  esac

  printf '\n# Proof@Home CLI\n%s\n' "$EXPORT_LINE" >> "$RC_FILE"
  info "Added to ${RC_FILE}"
}

# ── Phase 2: Prover toolchains ──

install_elan() {
  if command_exists elan; then
    success "elan already installed ($(elan --version 2>/dev/null | head -1))"
    return
  fi

  info "Installing elan (Lean 4 toolchain manager)..."
  if command_exists curl; then
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
  elif command_exists wget; then
    wget -qO- https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
  fi
  success "elan installed (Lean 4 toolchain manager)"
}

install_opam() {
  if command_exists opam; then
    success "opam already installed ($(opam --version 2>/dev/null))"
    return
  fi

  OS="$(uname -s)"
  echo ""
  info "opam requires a platform-specific installation:"
  echo ""
  case "$OS" in
    Darwin)
      if command_exists brew; then
        info "Running: brew install opam"
        brew install opam
        opam init -y --disable-sandboxing
        success "opam installed and initialized"
      else
        info "Install Homebrew first: https://brew.sh"
        info "Then run: brew install opam && opam init -y"
      fi
      ;;
    Linux)
      info "Install opam using your package manager:"
      info "  Ubuntu/Debian: sudo apt install opam && opam init -y"
      info "  Fedora:        sudo dnf install opam && opam init -y"
      info "  Or see: https://opam.ocaml.org/doc/Install.html"
      ;;
  esac
}

prompt_toolchains() {
  # Only prompt in interactive mode
  if [ ! -t 0 ]; then
    return
  fi

  if [ "$MINIMAL" = "1" ] || [ "$WITH_LEAN" = "1" ] || [ "$WITH_ROCQ" = "1" ]; then
    return
  fi

  echo ""
  echo "Which prover toolchains would you like to install?"
  echo ""
  echo "  1) Lean 4 (via elan)     — for Lean conjectures"
  echo "  2) Rocq (via opam)       — for Rocq/Coq conjectures"
  echo "  3) Both"
  echo "  4) Skip (install later with 'pah tools install')"
  echo ""
  printf "Choice [4]: "
  read -r choice

  case "$choice" in
    1) WITH_LEAN=1 ;;
    2) WITH_ROCQ=1 ;;
    3) WITH_LEAN=1; WITH_ROCQ=1 ;;
    *) ;;
  esac
}

install_toolchains() {
  if [ "$WITH_LEAN" = "1" ]; then
    install_elan
  fi
  if [ "$WITH_ROCQ" = "1" ]; then
    install_opam
  fi
  if [ "$WITH_LEAN" = "0" ] && [ "$WITH_ROCQ" = "0" ] && [ "$MINIMAL" = "0" ]; then
    if [ -t 0 ]; then
      info "You can install them later with 'pah tools install elan' or 'pah tools install opam'"
    fi
  fi
}

# ── Phase 3: Summary ──

print_summary() {
  echo ""
  success "pah installed to ${BIN_DIR}/pah"
  if [ "$WITH_LEAN" = "1" ]; then
    success "elan installed (Lean 4 toolchain manager)"
  fi
  if [ "$WITH_ROCQ" = "1" ] && command_exists opam; then
    success "opam installed (Rocq/Coq package manager)"
  fi
  echo ""
  info "Run 'pah setting set' to configure your identity and API key."
  info "Run 'pah tools check' to verify all dependencies."
  echo ""

  SHELL_NAME="$(basename "${SHELL:-/bin/sh}")"
  case "$SHELL_NAME" in
    zsh)  info "Restart your shell or run: source ~/.zshrc" ;;
    bash) info "Restart your shell or run: source ~/.bashrc" ;;
    *)    info "Restart your shell or run: source ~/.profile" ;;
  esac
}

# ── Main ──

detect_platform
fetch_version
download_binary
setup_path
prompt_toolchains
install_toolchains
print_summary
