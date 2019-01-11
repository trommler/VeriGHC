.PHONY: coq clean

FOREIGN_HS_TO_COQ = 1
HS_TO_COQ_DIR = ext/hs-to-coq

include ext/hs-to-coq/common.mk

GHC = $(shell stack --stack-yaml ext/hs-to-coq/stack.yaml exec -- which ghc)
# For bootstrap we want to use the same GHC that we use in hs_to_coq.
# TODO: Add rule to build GHC up to stage 1(?)

coq: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: Makefile _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf .coqdepend.d
