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

Instr.v : ext/ghc/compiler/nativeGen/PPC/Instr.hs
	$(HS_TO_COQ)  --ghc-tree ext/ghc \
	--ghc "-this-unit-id ghc-8.6.3" \
	--ghc -hide-all-packages \
	-I ext/ghc/includes \
	-I ext/ghc/includes/dist \
	-I ext/ghc/includes/dist-derivedconstants/header \
	-I ext/ghc/includes/dist-ghcconstants/header \
	-I ext/ghc/compiler/. \
	-I ext/ghc/compiler/parser \
	-I ext/ghc/compiler/utils \
	-I ext/ghc/compiler/stage1 \
	-I ext/ghc/compiler/stage1/build/. \
	-I ext/ghc/compiler/stage1/build/parser \
	-I ext/ghc/compiler/stage1/build/utils \
	-I ext/ghc/compiler/stage1/build/stage1 \
	--ghc "-package-id array-0.5.2.0" \
	--ghc "-package-id base-4.11.1.0" \
	--ghc "-package-id binary-0.8.6.0" \
	--ghc "-package-id bytestring-0.10.8.2" \
	--ghc "-package-id containers-0.5.11.0" \
	--ghc "-package-id deepseq-1.4.3.0" \
	--ghc "-package-id directory-1.3.1.5" \
	--ghc "-package-id filepath-1.4.2" \
	--ghc "-package-id ghc-boot-8.6.3" \
	--ghc "-package-id ghc-boot-th-8.6.3" \
	--ghc "-package-id ghc-heap-8.6.3" \
	--ghc "-package-id ghci-8.6.3" \
	--ghc "-package-id hpc-0.6.0.3" \
	--ghc "-package-id process-1.6.3.0" \
	--ghc "-package-id template-haskell-2.14.0.0" \
	--ghc "-package-id terminfo-0.4.1.2" \
	--ghc "-package-id time-1.8.0.2" \
	--ghc "-package-id transformers-0.5.5.0" \
	--ghc "-package-id unix-2.7.2.2" \
	--ghc "-D STAGE=1" \
	--ghc "-package-db ext/ghc/libraries/bootstrapping.conf"  \
	--ghc -XHaskell2010 \
	--ghc -XNoImplicitPrelude \
	--ghc -no-user-package-db \
	--- \
	-i -i compiler/backpack -i compiler/basicTypes \
	-i compiler/cmm -i compiler/codeGen -i compiler/coreSyn \
	-i compiler/deSugar \
	-i compiler/ghci -i compiler/hsSyn -i compiler/iface \
	-i compiler/llvmGen \
	-i compiler/main -i compiler/nativeGen -i compiler/parser \
	-i compiler/prelude \
	-i compiler/profiling -i compiler/rename -i compiler/simplCore \
	-i compiler/simplStg -i compiler/specialise -i compiler/stgSyn \
	-i compiler/stranal -i compiler/typecheck -i compiler/types \
	-i compiler/utils \
	-i compiler/stage1/build -I compiler/stage1/build \
	-i compiler/stage1/build/./autogen -I compiler/stage1/build/./autogen \
	-optP-include -optPcompiler/stage1/build/./autogen/cabal_macros.h \
	-rtsopts \
	-odir compiler/stage1/build -hidir compiler/stage1/build \
	-stubdir compiler/stage1/build \
	--- \
	ext/ghc/compiler/nativeGen/PPC/Instr.hs

