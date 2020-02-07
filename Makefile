FOREIGN_HS_TO_COQ = 1
HS_TO_COQ_DIR = ext/hs-to-coq

include ext/hs-to-coq/common.mk

.PHONY: coq clean

coq: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: Makefile _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf .coqdepend.d

