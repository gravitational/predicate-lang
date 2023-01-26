all:

.PHONY: test
test:
	cd ../../predicate && \
	curl -sSL 'https://install.python-poetry.org' | python3 - && \
	poetry install

	cd ../predicate-lsp-server && npm ci && npm run compile

	cd ../vscode && npm ci
	npm test

