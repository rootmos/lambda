GHC_OPTS=-Wall

.PHONY: lambda
lambda: lambda.hs
	runhaskell -- $(GHC_OPTS) lambda.hs
