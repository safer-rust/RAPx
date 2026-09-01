FROM ubuntu:22.04
LABEL authors="vaynnecol"

ENV PATH=/root/.cargo/bin:${PATH}

RUN apt-get update && \
    apt-get install -y \
    curl \
    build-essential \
    git \
    ninja-build \
    clang \
    python3 \
    make \
    cmake && \
    rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y && \
    rustup toolchain install nightly --profile minimal && \
    rustup component add rustc-dev rust-src llvm-tools-preview rustfmt --toolchain nightly && \
    rustc --version && \
    apt-get remove -y curl && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY . .

RUN ./install.sh
