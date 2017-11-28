ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

default: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

.PHONY: default clean install
