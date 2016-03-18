GHC_OPTS=-Wall

.PHONY: lambda
lambda: lambda.hs LambdaParser.hs
	runhaskell -- $(GHC_OPTS) lambda.hs
	runhaskell -- $(GHC_OPTS) LambdaParser.hs

.PHONY: deps
deps:
	cabal install fgl

.PHONY: ghci
ghci:
	ghci lambda.hs
