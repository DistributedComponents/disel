default: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

TPCMain.d.byte: default
	ocamlbuild -libs unix -I extraction/TPC -I shims shims/TPCMain.d.byte

CalculatorMain.d.byte: default
	ocamlbuild -libs unix -I extraction/calculator -I shims shims/CalculatorMain.d.byte

.PHONY: default clean install
