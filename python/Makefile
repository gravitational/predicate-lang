all: hello

.PHONY: test
test:
	lint-python
	pytest --pyargs src/predicate

.PHONY: test-%
test-%:
	mypy src/predicate/test/test_$*.py
	pytest --pyargs src/predicate/test/test_$*.py

.PHONY: hello
hello:
	python3.9 experminents/hello.py

.PHONY: func
func:
	python3.9 experiments/func.py

.PHONY: rbac
rbac:
	python3.9 experiments/rbac.py

.PHONY: access
access:
	python3.9 experiments/access.py

.PHONY: map
map:
	python3.9 experiments/map.py

.PHONY: map-simple
map-simple:
	python3.9 experiments/map_simple.py

.PHONY: regexp
regexp:
	python3.9 experiments/regexp.py

