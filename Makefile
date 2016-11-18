default: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

TPCMain.d.byte: default
	ocamlbuild -libs unix -I extraction/TPC -I shims shims/TPCMain.d.byte

CalculatorMain.d.byte: default
	ocamlbuild -libs unix -I extraction/calculator -I shims shims/CalculatorMain.d.byte

.PHONY: default clean
