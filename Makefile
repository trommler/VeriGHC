OUT=lib

FOREIGN_HS_TO_COQ = 1
HS_TO_COQ_DIR = ext/hs-to-coq

include ext/hs-to-coq/common.mk

HANDMOD        =

MODULES        = CmmType

# These modules translate, but do not compile, at the moment and
# should not be processed by coq
BROKEN_MODULES =

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

all: coq

$(OUT)/README.md:
	mkdir -p $(OUT)
	mkdir -p deps
	> $@
	echo 'This directory contains a Coq’ified version of parts of GHC' >> $@
	echo 'Do not edit files here! Instead, look in `examples/ghc`.' >> $@

$(OUT)/edits:
	mkdir -p $(OUT)
	ln -fs ../edits $(OUT)/edits

$(OUT)/_CoqProject: $(OUT)/README.md Makefile
	> $@
	echo '-Q . ""' >> $@
	echo '-R ../ext/hs-to-coq/base ""' >> $@
	echo '-Q ../ext/hs-to-coq/base-thy  Proofs' >> $@
	echo '-Q ../ext/hs-to-coq/examples/containers/lib   ""' >> $@
	echo '-Q ../ext/hs-to-coq/examples/containers/theories  ""' >> $@
	echo '-Q ../ext/hs-to-coq/examples/transformers/lib  ""' >> $@
	echo '-Q ../ext/hs-to-coq/examples/ghc/lib  ""' >> $@
	echo $(filter-out $(addsuffix .v,$(BROKEN_MODULES)), $(VFILES)) >> $@

$(OUT)/Makefile: $(OUT)/README.md $(OUT)/_CoqProject $(OUTFILES) Makefile
	cd $(OUT); coq_makefile -f _CoqProject -o Makefile


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
	$(MAKE) -f CoqMakefile
	$(MAKE) -C $(OUT) -f Makefile OPT=$(COQFLAGS)

CoqMakefile: Makefile _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf .coqdepend.d

