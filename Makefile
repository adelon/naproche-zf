all: test lib

.PHONY: lib
lib:
	stack build
	time stack exec zf -- --log library/everything.tex -t 15 --uncached

.PHONY: dump
dump:
	stack build
	time stack exec zf -- --log library/everything.tex -t 15 --uncached --dump dump

.PHONY: build
build:
	stack build

.PHONY: test
test:
	stack test --test-arguments "--accept"
