STEEL_HOME ?= ../../../../..

.PHONY: all build byte run clean

all: run

include $(STEEL_HOME)/share/steel/Makefile.include

build: dune out/Main.ml out/TwoLockQueue.ml out/TwoLockQueueTest.ml
	$(FSTAR_EXE) --ocamlenv dune build Main.exe

byte: dune out/Main.ml out/TwoLockQueue.ml out/TwoLockQueueTest.ml
	$(FSTAR_EXE) --ocamlenv dune build Main.bc

run: build
	_build/default/Main.exe

clean::
	$(FSTAR_EXE) --ocamlenv dune clean