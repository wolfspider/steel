# ----- Config -----
STEEL_HOME ?= ../../../../..

FSTAR      ?= fstar.exe
OCAMLFIND  ?= ocamlfind
OCAMLC     ?= ocamlc

# Make sure F* can find your files + Steel; don't mark PingPongTest as cached
FSTAR_OPTIONS := --include . --include .. --already_cached '*,-PingPongTest'

# Bring in Steel’s rules (adds include paths, etc.)
include $(STEEL_HOME)/share/steel/Makefile.include

CACHE_DIR := .fstar_cache

# ----- Phonies -----
.PHONY: all check ml build run clean clean-local

all: run

# 0) Ensure dirs exist
out:
	mkdir -p out
$(CACHE_DIR):
	mkdir -p $(CACHE_DIR)

# 1) CHECK: verify PingPongTest first (fills cache)
check: $(CACHE_DIR)/.stamp
$(CACHE_DIR)/.stamp: PingPongTest.fst | $(CACHE_DIR)
	$(FSTAR) $(FSTAR_OPTIONS) --cache_dir $(CACHE_DIR) --cache_checked_modules PingPongTest.fst
	@touch $@

# 2) EXTRACT: now that it's checked, extract to OCaml
ml: out/.ml.stamp
out/.ml.stamp: PingPongTest.fst check | out
	$(FSTAR) $(FSTAR_OPTIONS) --cache_dir $(CACHE_DIR) --cache_checked_modules \
	  --codegen OCaml --odir out PingPongTest.fst
	@printf '%s\n' \
'let () =' \
'  print_endline "PingPongTest extracted (OCaml)";' \
> out/Main.ml
	@touch $@

# 3) Build the bytecode exe from everything in out/
OCAML_SRCS := $(wildcard out/*.ml)
OCAML_CMOS := $(patsubst out/%.ml,out/%.cmo,$(OCAML_SRCS))

out/%.cmo: out/%.ml
	$(OCAMLFIND) $(OCAMLC) -package fstarlib -linkpkg -I out -c $< -o $@

build: ml $(OCAML_CMOS)
	$(OCAMLFIND) $(OCAMLC) -package fstarlib -linkpkg -I out $(OCAML_CMOS) -o pingpong_ml.byte

run: build
	./pingpong_ml.byte

# Clean
clean:: clean-local
clean-local:
	rm -rf out pingpong_ml.byte $(CACHE_DIR)
