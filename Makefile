MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all config tags install

COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

all: $(COQMAKEFILE)
	$(COQMAKE) all

$(COQMAKEFILE) config:
	$(COQBIN)coq_makefile -f Make  -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(COQMAKE) clean

dist:
	mkdir newtonsums
	cp *.v Makefile Make _CoqProject opam newtonsums/
	tar zcvf newtonsums.tgz newtonsums/
	rm -rf newtonsums/

install: $(COQMAKEFILE)
	$(COQMAKE) install

%: Makefile.coq
	$(COQMAKE) $@
