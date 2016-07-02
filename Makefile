.PHONY: run
run:
	stack exec lambda

.PHONY: test
test:
	stack test
