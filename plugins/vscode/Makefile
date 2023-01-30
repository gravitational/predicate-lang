all:

.PHONY: test
test:
	cd ../lsp-server && npm ci && npm run compile
	cd ../vscode && npm ci
	npm test

