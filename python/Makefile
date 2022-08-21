all: hello

.PHONY: test
test:
	mypy src/predicate/
	pytest --pyargs src/predicate


.PHONY: test-teleport
test-teleport:
	mypy src/predicate/test/test_teleport.py
	pytest --pyargs src/predicate/test/test_teleport.py

.PHONY: test-ast
test-ast:
	mypy src/predicate/test/test_ast.py
	pytest --pyargs src/predicate/test/test_ast.py

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

