#!/usr/bin/env bash

CODE_TESTS_PATH="$(pwd)/out/test/suite/index"
CODE_TESTS_WORKSPACE="$(pwd)/test/testFixture"

export CODE_TESTS_PATH
export CODE_TESTS_WORKSPACE

node "$(pwd)/out/test/runTest"