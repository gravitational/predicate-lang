all:

.PHONY: test
test:
	cd ../predicate-lsp-server && npm ci
	npm run compile

	cd ../vscode
	npm ci
	npm test

