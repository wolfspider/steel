# ----- Config -----
STEEL_HOME ?= ../../../../..

FSTAR_EXE  ?= fstar.exe
OCAMLFIND  ?= ocamlfind
OCAMLC     ?= ocamlc

# Extra paths for this project.
# Do NOT add --already_cached for our own modules.
FSTAR_OPTIONS := --include . --include ..

# Steel adds:
#   --cache_checked_modules
#   --already_cached 'Prims,FStar,LowStar,Steel,C'
#   --include $(STEEL_HOME)/lib/steel
#   --load_cmxs steel
#
# It also defines .checked dependency rules and the "verify" target.
include $(STEEL_HOME)/share/steel/Makefile.include

# ----- Project modules -----
FST_SRCS := \
	Trees.fst \
	Selectors.Tree.Core.fst \
	Selectors.Tree.fst \
	Model.fst \
	Domain.fst \
	MultiCollaboration.fst \
	EffectStateMachine.fst \
	EffectSystemProperties.fst \
	RealTimeCollaboration.fst \
	LeaderCluster.fst \
	PingPongTest.fst

# ----- Phonies -----
.PHONY: all check ml build run clean-local

all: run

out:
	mkdir -p out

# ------------------------------------------------------------
# 1) VERIFY
#
# Use Steel's own verification machinery.
#
# Makefile.include automatically includes all *.fst/*.fsti files
# in the current directory in FSTAR_FILES and builds the .checked
# dependency graph.
# ------------------------------------------------------------

check: verify

# ------------------------------------------------------------
# 2) EXTRACT
#
# All project files have already been verified before extraction.
# The .checked files now exist where F* expects them.
# ------------------------------------------------------------

ml: out/.ml.stamp

out/.ml.stamp: check $(FST_SRCS) | out
	@set -e; \
	for f in $(FST_SRCS); do \
		echo "== EXTRACT $$f =="; \
		$(FSTAR_EXE) $(FSTAR_OPTIONS) $(COMPAT_INDEXED_EFFECTS) \
			--codegen OCaml \
			--odir out \
			$$f; \
	done

	@printf '%s\n' \
	'let () =' \
	'  print_endline "PingPongTest extracted (OCaml)";' \
	> out/Main.ml

	@touch $@

# ------------------------------------------------------------
# 3) Build extracted OCaml
# ------------------------------------------------------------

OCAML_SRCS = $(wildcard out/*.ml)
OCAML_CMOS = $(patsubst out/%.ml,out/%.cmo,$(OCAML_SRCS))

out/%.cmo: out/%.ml
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c $< \
		-o $@

build: ml
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/Trees.ml \
		-o out/Trees.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/Selectors_Tree_Core.ml \
		-o out/Selectors_Tree_Core.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/Selectors_Tree.ml \
		-o out/Selectors_Tree.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/Model.ml \
		-o out/Model.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/Domain.ml \
		-o out/Domain.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/MultiCollaboration.ml \
		-o out/MultiCollaboration.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/EffectStateMachine.ml \
		-o out/EffectStateMachine.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/EffectSystemProperties.ml \
		-o out/EffectSystemProperties.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/RealTimeCollaboration.ml \
		-o out/RealTimeCollaboration.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/LeaderCluster.ml \
		-o out/LeaderCluster.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/PingPongTest.ml \
		-o out/PingPongTest.cmo
	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		-c out/Main.ml \
		-o out/Main.cmo

	$(OCAMLFIND) $(OCAMLC) \
		-package fstarlib \
		-linkpkg \
		-I out \
		out/Trees.cmo \
		out/Selectors_Tree_Core.cmo \
		out/Selectors_Tree.cmo \
		out/Model.cmo \
		out/Domain.cmo \
		out/MultiCollaboration.cmo \
		out/EffectStateMachine.cmo \
		out/EffectSystemProperties.cmo \
		out/RealTimeCollaboration.cmo \
		out/LeaderCluster.cmo \
		out/PingPongTest.cmo \
		out/Main.cmo \
		-o pingpong_ml.byte

run: build
	./pingpong_ml.byte

clean:: clean-local

clean-local:
	rm -rf out pingpong_ml.byte