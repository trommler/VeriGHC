.PHONY: coq clean

FOREIGN_HS_TO_COQ = 1
HS_TO_COQ_DIR = ext/hs-to-coq

include ext/hs-to-coq/common.mk

OUT = native
# For bootstrap we want to use the same GHC that we use in hs_to_coq.
GHC = $(shell stack --stack-yaml ext/hs-to-coq/stack.yaml exec -- which ghc)
# TODO: Add rule to build GHC up to stage 1(?)

$(OUT)/Instr.v : ext/ghc/compiler/nativeGen/PPC/Instr.hs
	$(HS_TO_COQ) \
	--ghc-tree ext/ghc \
	--ghc "-this-unit-id ghc-8.4.3" \
	--ghc -hide-all-packages \
	-I ext/ghc/includes \
	-I ext/ghc/includes/dist \
	-I ext/ghc/includes/dist-derivedconstants/header \
	-I ext/ghc/includes/dist-ghcconstants/header \
	-i ext/ghc/compiler/backpack \
	-i ext/ghc/compiler/basicTypes \
	-i ext/ghc/compiler/cmm \
	-i ext/ghc/compiler/codeGen \
	-i ext/ghc/compiler/coreSyn \
	-i ext/ghc/compiler/deSugar \
	-i ext/ghc/compiler/ghci \
	-i ext/ghc/compiler/hsSyn \
	-i ext/ghc/compiler/iface \
	-i ext/ghc/compiler/llvmGen \
	-i ext/ghc/compiler/main \
	-i ext/ghc/compiler/nativeGen \
	-i ext/ghc/compiler/parser \
	-i ext/ghc/compiler/prelude \
	-i ext/ghc/compiler/profiling \
	-i ext/ghc/compiler/rename \
	-i ext/ghc/compiler/simplCore \
	-i ext/ghc/compiler/simplStg \
	-i ext/ghc/compiler/specialise \
	-i ext/ghc/compiler/stgSyn \
	-i ext/ghc/compiler/stranal \
	-i ext/ghc/compiler/typecheck \
	-i ext/ghc/compiler/types \
	-i ext/ghc/compiler/utils \
	-i ext/ghc/compiler/vectorise \
	-i ext/ghc/compiler/stage1/build \
	-I ext/ghc/compiler/. \
	-I ext/ghc/compiler/parser \
	-I ext/ghc/compiler/utils \
	-I ext/ghc/compiler/stage1 \
	-I ext/ghc/compiler/stage1/build \
	-I ext/ghc/compiler/stage1/build/parser \
	-I ext/ghc/compiler/stage1/build/utils \
	-I ext/ghc/compiler/stage1/build/stage1 \
	-i ext/ghc/compiler/stage1/build \
	-I ext/ghc/compiler/stage1/build \
	-i ext/ghc/compiler/stage1/build/./autogen \
	-I ext/ghc/compiler/stage1/build/./autogen \
	--ghc -XHaskell2010 \
	--ghc -XNoImplicitPrelude \
	--ghc -no-user-package-db \
	--ghc -optP-include \
	--ghc -optPext/ghc/compiler/stage1/build/./autogen/cabal_macros.h \
	--ghc "-package-id array-0.5.2.0" \
	--ghc "-package-id base-4.11.1.0" \
	--ghc "-package-id bytestring-0.10.8.2" \
	--ghc "-package-id binary-0.8.5.1" \
	--ghc "-package-id containers-0.5.11.0" \
	--ghc "-package-id deepseq-1.4.3.0" \
	--ghc "-package-id directory-1.3.1.5" \
	--ghc "-package-id filepath-1.4.2" \
	--ghc "-package-id ghc-boot-8.4.3" \
	--ghc "-package-id ghc-boot-th-8.4.3" \
	--ghc "-package-id ghci-8.4.3" \
	--ghc "-package-id hpc-0.6.0.3" \
	--ghc "-package-id process-1.6.3.0" \
	--ghc "-package-id template-haskell-2.13.0.0" \
	--ghc "-package-id terminfo-0.4.1.1" \
	--ghc "-package-id time-1.8.0.2" \
	--ghc "-package-id transformers-0.5.5.0" \
	--ghc "-package-id unix-2.7.2.2" \
	--ghc "-D STAGE=1" \
	--ghc -v \
	-N \
	-e edits \
	-o $(OUT) \
	ext/ghc/compiler/nativeGen/PPC/Instr.hs

coq: CoqMakefile
	$(MAKE) -f CoqMakefile

CoqMakefile: Makefile _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:: CoqMakefile
	$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf .coqdepend.d

