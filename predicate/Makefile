all:

.PHONY: test-%
test-%:
	mypy solver/test/test_$*.py
	pytest --pyargs solver/test/test_$*.py

.PHONY: lint
lint:
	lint-python

.PHONY: check
check:
	lint-python --check

.PHONY: test
test:
	pytest --pyargs solver
