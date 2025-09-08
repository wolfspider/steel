# Use Steel’s workspace and F*’s ocamlenv wrapper so dune can find fstar.lib
STEEL_HOME ?= ../../../../..

.PHONY: all build run clean

all: run

# Keep the include so $(FSTAR_EXE) is set
include $(STEEL_HOME)/share/steel/Makefile.include

# Build the already-extracted OCaml in ./out with dune (bytecode is fine)
build: dune out/Main.ml out/Duplex_PingPongTest.ml out/Duplex_PingPongTest.ml
	$(FSTAR_EXE) --ocamlenv dune build

run: build
	_build/default/Main.exe

clean::
	$(FSTAR_EXE) --ocamlenv dune clean
