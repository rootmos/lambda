.PHONY: run
run:
	cabal run

.PHONY: test
test:
	cabal test --show-details=always --test-option=--color
