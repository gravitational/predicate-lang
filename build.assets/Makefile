PROTOC_VER ?= 3.6.1
PROTOC_PLATFORM := linux-x86_64
GOGO_PROTO_TAG ?= v1.3.2
GO_RUNTIME ?= go1.16.2
RUST_VERSION ?= 1.53.0
RUST_ARCH ?= x86_64-unknown-linux-gnu
UID := $$(id -u)
GID := $$(id -g)
HOSTNAME ?= buildbox

BUILDBOX ?= acre-buildbox:0.0.1
SRCDIR ?= /go/src/github.com/gravitational/acre
GOMODCACHE ?= /tmp/gomodcache
DOCKERFLAGS := --rm=true -v "$$(pwd)/../":$(SRCDIR) -v /tmp:/tmp -w $(SRCDIR) -h $(HOSTNAME) -e GOMODCACHE=$(GOMODCACHE)

# grpc generates GRPC stubs from service definitions
.PHONY: grpc
grpc: buildbox
	docker run \
		$(DOCKERFLAGS) -t $(BUILDBOX) \
		make -C /go/src/github.com/gravitational/acre buildbox-grpc

#
# Builds a Docker container which is used for building official Teleport binaries
# If running in CI and there is no image with the buildbox name:tag combination present locally,
# the image is pulled from the Docker repository. If this pull fails (i.e. when a new Go runtime is
# first used), the error is ignored and the buildbox is built using the Dockerfile.
#
.PHONY:buildbox
buildbox:
	docker build \
			--build-arg UID=$(UID) \
			--build-arg GID=$(GID) \
			--build-arg GO_RUNTIME=$(GO_RUNTIME) \
			--build-arg PROTOC_VER=$(PROTOC_VER) \
			--build-arg GOGO_PROTO_TAG=$(GOGO_PROTO_TAG) \
			--build-arg PROTOC_PLATFORM=$(PROTOC_PLATFORM) \
			--build-arg RUSTUP_VERSION=$(RUSTUP_VERSION) \
			--build-arg RUST_VERSION=$(RUST_VERSION) \
			--build-arg RUST_ARCH=$(RUST_ARCH) \
			--tag $(BUILDBOX) . ;
