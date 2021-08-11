CLANG ?= $(shell which clang || which clang-10)
CLANG_FORMAT ?= $(shell which clang-format || which clang-format-10)

.PHONY: all
all: build clean gorun

.PHONY: gorun
gorun:
	go build main.go && ./main

.PHONY: run
run:
	./target/debug/predicate

.PHONY: build
build:
	cargo build --target=wasm32-unknown-unknown

.PHONY: predicate
predicate:
	cargo build --bin predicate

.PHONY: clean
clean:
	wasm-gc target/wasm32-unknown-unknown/debug/acre.wasm

# grpc generates GRPC stubs from service definitions
.PHONY: grpc
grpc:
	make -C build.assets grpc

# buildbox-grpc generates GRPC stubs inside buildbox
.PHONY: buildbox-grpc
buildbox-grpc:
# standard GRPC output
	echo $$PROTO_INCLUDE
	find api/ -iname *.proto | xargs $(CLANG_FORMAT) -i -style='{ColumnLimit: 100, IndentWidth: 4, Language: Proto}'

	protoc -I=.:$$PROTO_INCLUDE \
		--proto_path=api/types \
		--gogofast_out=plugins=grpc:pkg/types \
		hello.proto

	protoc -I=.:$$PROTO_INCLUDE \
		--proto_path=api/types \
		--rust_out ./src \
		hello.proto
