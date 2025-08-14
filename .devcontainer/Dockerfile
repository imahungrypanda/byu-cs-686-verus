FROM debian:sid

# Install system dependencies (except nodejs/npm — we install them separately)
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    pkg-config \
    libssl-dev \
    ca-certificates \
    python3 \
    unzip \
    locales \
    && sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen \
    && locale-gen \
    && rm -rf /var/lib/apt/lists/*

# Install Node.js 18.x and global npm packages
RUN curl -fsSL https://deb.nodesource.com/setup_18.x | bash - && \
    apt-get update && apt-get install -y nodejs && \
    npm install -g @vscode/vsce esbuild

# Create non-root user
RUN useradd -ms /bin/bash vscode
USER vscode

# Build z3
RUN git clone https://github.com/Z3Prover/z3.git /home/vscode/z3 && \
    cd /home/vscode/z3 && \
    git fetch origin tag z3-4.12.5 && \
    git checkout -b z3-4.12.5 tags/z3-4.12.5 && \
    python3 scripts/mk_make.py && \
    cd /home/vscode/z3/build && \
    make

# Install z3 binary
USER root
RUN cd /home/vscode/z3/build && \
    make install
USER vscode
ENV VERUS_Z3_PATH="/usr/bin/z3"

# Set up Rust
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
ENV PATH="/home/vscode/.cargo/bin:${PATH}"

# Install Verusfmt
RUN cargo install verusfmt

# Build Verus and vstd
RUN rm -rf /home/vscode/verus && \
    git clone --recurse-submodules https://github.com/verus-lang/verus /home/vscode/verus

RUN bash -l -c "cd /home/vscode/verus/source && source ../tools/activate && vargo build --release"

ENV VERUSROOT="/home/vscode/verus"
ENV PATH="/home/vscode/verus/source/target-verus/release:${PATH}"

# Clone Verus Analyzer
RUN rm -rf /home/vscode/verus-analyzer && \
    git clone --recursive https://github.com/verus-lang/verus-analyzer /home/vscode/verus-analyzer

# Install local JS dependencies for the VS Code extension
WORKDIR /home/vscode/verus-analyzer/editors/code
RUN npm install vscode-languageclient

# Build Verus Analyzer server and package VSIX
WORKDIR /home/vscode/verus-analyzer
RUN cargo xtask dist --proof-action --client-patch-version 42

# Adjust target as needed for your container arch
WORKDIR /home/vscode/verus-analyzer/editors/code
RUN ARCH=$(uname -m) && \
    case "$ARCH" in \
      x86_64) VSCE_TARGET="linux-x64"; OUT_ARCH="x86_64-unknown-linux-gnu" ;; \
      aarch64) VSCE_TARGET="linux-arm64"; OUT_ARCH="aarch64-unknown-linux-gnu" ;; \
      *) echo "Unsupported architecture: $ARCH" && exit 1 ;; \
    esac && \
    echo "🏗 Building for $VSCE_TARGET" && \
    npx vsce package \
        -o "../../dist/verus-analyzer-${OUT_ARCH}.vsix" \
        --target "$VSCE_TARGET"

# Install pip and pre-commit
USER root
RUN apt-get update && apt-get install -y python3-pip python3.13-venv

USER vscode
ENV PRECOMMIT_VENV=/home/vscode/.precommit-venv
RUN python3 -m venv $PRECOMMIT_VENV && \
    $PRECOMMIT_VENV/bin/pip install --upgrade pip && \
    $PRECOMMIT_VENV/bin/pip install pre-commit

# Add to PATH so pre-commit is available
ENV PATH="${PRECOMMIT_VENV}/bin:${PATH}"
