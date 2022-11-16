all: lint test

.PHONY: test-%
test-%:
	pytest --pyargs solver/test/test_$*.py

.PHONY: lint
lint:
	lint-python

.PHONY: lint-check
lint-check:
	lint-python --check

.PHONY: test
test:
	pytest --pyargs solver
