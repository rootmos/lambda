GHC_OPTS=-Wall

.PHONY: lambda
lambda: lambda.hs
	runhaskell -- $(GHC_OPTS) lambda.hs

.PHONY: deps
deps:
	cabal install fgl

.PHONY: ghci
ghci:
	ghci lambda.hs
