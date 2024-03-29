export V=1

OUT=lib

FOREIGN_HS_TO_COQ = 1
HS_TO_COQ_DIR = ext/hs-to-coq

include $(HS_TO_COQ_DIR)/common.mk

HANDMOD        = \
   FastString \
   AxiomatizedTypes \
   IntMap \
   Hoopl/Block \
   Hoopl/Graph \

UTILS          = \
   Util \
   SrcLoc \
   Unique \
   UniqSupply \
   BasicTypes \
   DynFlags \
   Panic \
   OccName \
   Module \
   EnumSet \
   UniqFM \
   UniqSet \
   FiniteMap \
   Maybes \
   Name \
   Literal \
   CoreSyn \
   OrdList \

CMM2PPC        = \
   CmmType \
   CLabel \
   CmmMachOp \
   Hoopl/Unique \
   Hoopl/Label \
   BlockId \
   CmmExpr \
   CmmSwitch \
   SMRep \
   CmmNode \
   Cmm \
   Format \
   RegClass \
   Reg \
   PPC/Regs \
   PPC/Cond \
   Instruction \
   Platform \
   PPC/Instr \
   Debug \
   NCGMonad \
   PIC \
   PprCmmExpr \
   TargetReg \

MODULES        = \
   $(UTILS) \
   $(CMM2PPC) \

# These modules translate, but do not compile, at the moment and
# should not be processed by coq
BROKEN_MODULES = \

VFILES_GEN     = $(addsuffix .v,$(MODULES))
VFILES_MAN     = $(addsuffix .v,$(HANDMOD))

VFILES         = $(VFILES_GEN) $(VFILES_MAN)

OUTFILES_GEN   = $(addprefix $(OUT)/,$(VFILES_GEN))
OUTFILES_MAN   = $(addprefix $(OUT)/,$(VFILES_MAN))

OUTFILES       = $(OUTFILES_GEN) $(OUTFILES_MAN)

HSFILES        = $(addsuffix .hs,$(MODULES))
HSFILESPATH    = $(addprefix ghc/compiler/*/,$(HSFILES))

EDITPATHS      = $(addprefix module-edits/,$(MODULES))
EDITFILES      = edits $(addsuffix /edits,$(EDITPATHS)) $(addsuffix /*.v, $(EDITPATHS))


.PHONY: coq clean

all: vfiles coq

vfiles : $(OUT)/edits $(OUT)/Makefile $(OUTFILES)

.stamp-hs-to-coq: .git/modules/ext/hs-to-coq/HEAD
	cd $(HS_TO_COQ_DIR) && stack setup && stack build
	$(MAKE) -f HsToCoqMakefile all
	touch $@

$(OUT)/README.md:
	mkdir -p $(OUT)
	mkdir -p deps
	> $@
	echo 'This directory contains a Coq’ified version of parts of GHC' >> $@
	echo 'Do not edit files here! Instead, look in `examples/ghc`.' >> $@

$(OUT)/edits:
	mkdir -p $(OUT)
	ln -fs ../edits $(OUT)/edits

$(OUT)/_CoqProject: $(OUT)/README.md Makefile .stamp-hs-to-coq
	> $@
	echo '-R . ""' >> $@
	echo '-Q ../ext/hs-to-coq/base ""' >> $@
	echo '-Q ../ext/hs-to-coq/base-thy  Proofs' >> $@
	echo '-Q ../ext/hs-to-coq/examples/containers/lib   ""' >> $@
	echo '-Q ../ext/hs-to-coq/examples/containers/theories  ""' >> $@
	echo '-Q ../ext/hs-to-coq/examples/transformers/lib  ""' >> $@
	echo $(filter-out $(addsuffix .v,$(BROKEN_MODULES)), $(VFILES)) >> $@

$(OUT)/Makefile: $(OUT)/README.md $(OUT)/_CoqProject $(OUTFILES) Makefile
	cd $(OUT); $(COQMAKEFILE) -f _CoqProject -o Makefile

$(OUT)/CoqMakefile.local: $(OUT)/README.md CoqMakefile.local
	cp CoqMakefile.local $@

HS_TO_COQ_GHC_OPTS=\
     --ghc-tree ext/hs-to-coq/examples/ghc/ghc \
     -i ext/hs-to-coq/examples/ghc/gen-files \
     -I ext/hs-to-coq/examples/ghc/gen-files \
     -I ext/hs-to-coq/examples/ghc/ghc/includes \
     -I ext/hs-to-coq/examples/ghc/ghc/compiler \
     --ghc -DSTAGE=2 \
     --ghc -package=ghc-boot-th \
     --ghc -XNoImplicitPrelude \
     -e ext/hs-to-coq/base/edits \
     -e ext/hs-to-coq/examples/containers/edits \
     -e ext/hs-to-coq/examples/transformers/edits \
     --iface-dir ext/hs-to-coq/base \
     --iface-dir ext/hs-to-coq/examples/containers/lib \
     --iface-dir ext/hs-to-coq/examples/transformers/lib \
     --iface-dir $(OUT) \
     --dependency-dir deps \
     -e edits \
     -N \

-include deps/*mk

%.h2ci: %.v
	test -e $@

.SECONDEXPANSION:
$(OUTFILES_GEN): $(OUT)/%.v : $$(wildcard module-edits/$$*/preamble.v) $$(wildcard module-edits/$$*/midamble.v)  $$(wildcard module-edits/$$*/edits) edits
	$(HS_TO_COQ) $(addprefix -e , $(wildcard module-edits/$*/edits)) \
	             $(addprefix -p , $(wildcard module-edits/$*/preamble.v)) \
	             $(addprefix --midamble , $(wildcard module-edits/$*/midamble.v)) \
		     $(HS_TO_COQ_GHC_OPTS) \
                     -o $(OUT) \
		     $(word 1,$(wildcard ghc-head/$*.hs ext/hs-to-coq/examples/ghc/ghc/compiler/*/$*.hs))
	test -e $@

$(OUTFILES_MAN): $(OUT)/%.v : manual/%.v
	mkdir -p "$$(dirname $(OUT)/$*.v)"
	rm -f $@
	lndir ../manual $(OUT)/


coq: CoqMakefile $(OUT)/Makefile $(OUTFILES)
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)
	$(MAKE) -f CoqMakefile

CoqMakefile: Makefile _CoqProject
	$(COQMAKEFILE) -f _CoqProject -o $@

clean:: CoqMakefile
	rm -f .stamp-hs-to-coq
	rm -rf $(OUT) deps
	$(MAKE) -f HsToCoqMakefile clean
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf .coqdepend.d

# Install build-dependencies
OPAMFILES=$(wildcard *.opam)
BUILDDEPFILES=$(addsuffix -builddep.opam, $(addprefix builddep/,$(basename $(OPAMFILES))))

builddep/%-builddep.opam: %.opam Makefile
	@echo "# Creating builddep package for $<."
	@mkdir -p builddep
	@sed <$< -E 's/^(build|install|remove):.*/\1: []/; s/"(.*)"(.*= *version.*)$$/"\1-builddep"\2/;' >$@

builddep-opamfiles: $(BUILDDEPFILES)
.PHONY: builddep-opamfiles

OPAMSWITCH=$(shell pwd)/.verighc
OPAMFLAGS+=--switch $(OPAMSWITCH)
COQMAKEFILE=opam exec $(OPAMFLAGS) coq_makefile --

builddep: builddep-opamfiles .verighc
	@# We want opam to not just install the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing builddep packages."
	@opam install --yes $(OPAMFLAGS) $(BUILDDEPFILES)
.PHONY: builddep

.verighc:
	opam switch create $@
	opam repo add $(OPAMFLAGS) coq-released "https://coq.inria.fr/opam/released"
	opam repo add $(OPAMFLAGS) iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
