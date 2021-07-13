# This Dockerfile makes the "build box": the container used to build official
# releases of Teleport and its documentation.

# Use Ubuntu 18.04 as base to get an older glibc version.
# Using a newer base image will build against a newer glibc, which creates a
# runtime requirement for the host to have newer glibc too. For example,
# teleport built on any newer Ubuntu version will not run on Centos 7 because
# of this.
FROM ubuntu:18.04

ENV LANGUAGE="en_US.UTF-8" \
    LANG="en_US.UTF-8" \
    LC_ALL="en_US.UTF-8" \
    LC_CTYPE="en_US.UTF-8" \
    DEBIAN_FRONTEND="noninteractive"

# Install packages.
# We install curl first to allow setting up the Google SDK as part of the same layer.
RUN apt-get update -y --fix-missing && \
    apt-get -q -y upgrade && \
    apt-get install -y --no-install-recommends apt-utils ca-certificates curl gnupg && \
    apt-get -y update && \
    apt-get install -q -y --no-install-recommends \
        build-essential \
        clang-10 \
        clang-format-10 \        
        apt-utils \
        curl \
        git \
        gzip \
        locales \
        make \
        pkg-config \
        tar \
        tree \
        unzip \
        zip \
        && \
    dpkg-reconfigure locales && \
    apt-get -y clean && \
    rm -rf /var/lib/apt/lists/*

ARG UID
ARG GID
RUN (groupadd ci --gid=$GID -o && useradd ci --uid=$UID --gid=$GID --create-home --shell=/bin/sh && \
     mkdir -p -m0700 /var/lib/teleport && chown -R ci /var/lib/teleport)

# Install Go.
ARG GO_RUNTIME
RUN mkdir -p /opt && cd /opt && curl https://storage.googleapis.com/golang/$GO_RUNTIME.linux-amd64.tar.gz | tar xz && \
    mkdir -p /go/src/github.com/gravitational/acre && \
    chmod a+w /go && \
    chmod a+w /var/lib && \
    chmod a-w /

ENV GOPATH="/go" \
    GOROOT="/opt/go" \
    PATH="$PATH:/opt/go/bin:/go/bin:/go/src/github.com/gravitational/acre/build"

# Install rust
ARG RUST_VERSION
ARG RUST_ARCH

ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:$HOME/.cargo/bin:$PATH:$PATH \
    RUST_VERSION=${RUST_VERSION}

RUN curl -L -o /tmp/rustup-init https://static.rust-lang.org/rustup/dist/${RUST_ARCH}/rustup-init && \
   chmod +x /tmp/rustup-init && \
   /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain ${RUST_VERSION} --default-host ${RUST_ARCH} && \
   rustup --version && \
   cargo --version && \
   rustc --version && \
   chmod -R a+w $RUSTUP_HOME $CARGO_HOME;

RUN cargo install protobuf-codegen;

# Install protobuf and grpc build tools.
ARG PROTOC_VER
ARG PROTOC_PLATFORM
ARG GOGO_PROTO_TAG

ENV PROTOC_TARBALL protoc-${PROTOC_VER}-${PROTOC_PLATFORM}.zip
ENV GOGOPROTO_ROOT ${GOPATH}/src/github.com/gogo/protobuf

RUN (curl -L -o /tmp/${PROTOC_TARBALL} https://github.com/google/protobuf/releases/download/v${PROTOC_VER}/${PROTOC_TARBALL} && \
     cd /tmp && unzip /tmp/${PROTOC_TARBALL} -d /usr/local && \
     rm /tmp/${PROTOC_TARBALL})
RUN (git clone https://github.com/gogo/protobuf.git ${GOPATH}/src/github.com/gogo/protobuf && go install golang.org/x/tools/cmd/goimports@latest && \
     cd ${GOPATH}/src/github.com/gogo/protobuf && \
     git reset --hard ${GOGO_PROTO_TAG} && \
     make install)

ENV PROTO_INCLUDE "/usr/local/include":"${GOPATH}/src":"${GOPATH}/src/github.com/gogo/protobuf/protobuf":"${GOGOPROTO_ROOT}":"${GOGOPROTO_ROOT}/protobuf":"${GOPATH}/src/github.com/gravitational/acre/api/types"
