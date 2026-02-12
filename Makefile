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

.PHONE: profile
profile:
	stack --work-dir .stack-work-profile build --profile --ghc-options "-fprof-auto -fprof-cafs"
	stack --work-dir .stack-work-profile exec --profile zf -- library/formalizations_with_section_20_up_to_euclidean_metric_theorem.tex --uncached +RTS -s -p
	ghc-prof-flamegraph zf.prof

.PHONE: profilenominal
profilenominal:
	stack --work-dir .stack-work-profile build --profile --ghc-options "-fprof-auto -fprof-cafs"
	stack --work-dir .stack-work-profile exec --profile zf -- library/formalizations_with_section_20_up_to_euclidean_metric_theorem.tex --nominal --uncached +RTS -s -p
	ghc-prof-flamegraph zf.prof

.PHONE: profilemem
profilemem:
	stack --work-dir .stack-work-profile build --profile --ghc-options "-fprof-auto -fprof-cafs"
	stack --work-dir .stack-work-profile exec --profile zf -- library/formalizations_with_section_20_up_to_euclidean_metric_theorem.tex --uncached +RTS -hc -RTS
	hp2ps zf.hp

.PHONE: profileparser
profileparser:
	stack --work-dir .stack-work-profile build --profile --ghc-options "-fprof-auto -fprof-cafs"
	stack --work-dir .stack-work-profile exec --profile zf -- library/formalizations_with_section_20_up_to_euclidean_metric_theorem.tex --parseonly --uncached +RTS -p
	ghc-prof-flamegraph zf.prof
