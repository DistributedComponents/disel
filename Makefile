OCAMLBUILD = ocamlbuild -tag safe_string -libs unix -I shims

default: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	$(OCAMLBUILD) -clean

tpc: TPCMain.native

calculator: CalculatorMain.native

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

TPCMain.d.byte: default
	$(OCAMLBUILD) -I extraction/TPC shims/TPCMain.d.byte

TPCMain.native: default
	$(OCAMLBUILD) -I extraction/TPC shims/TPCMain.native

CalculatorMain.d.byte: default
	$(OCAMLBUILD) -I extraction/calculator shims/CalculatorMain.d.byte

CalculatorMain.native: default
	$(OCAMLBUILD) -I extraction/calculator shims/CalculatorMain.native

.PHONY: default clean install tpc calculator
