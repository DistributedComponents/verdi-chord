COQVERSION := $(shell coqc --version|grep "version 8.5")

ifeq "$(COQVERSION)" ""
$(error "Verdi is only compatible with Coq version 8.5")
endif

COQPROJECT_EXISTS=$(wildcard _CoqProject)
ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

CHECKPATH := $(shell ./script/checkpaths.sh)

ifneq ("$(CHECKPATH)","")
$(info $(CHECKPATH))
$(warning checkpath reported an error)
endif

MLFILES = extraction/chord/coq/ExtractedChord.ml extraction/chord/coq/ExtractedChord.mli \
	extraction/chord/coq/ExtractedChordShed.ml extraction/chord/coq/ExtractedChordShed.mli

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq \
	  -extra '$(MLFILES)' \
	    'extraction/chord/coq/ExtractChord.v systems/Chord.vo shed/ChordShed.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/chord/coq/ExtractChord.v'

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq

chord: $(MLFILES)
	$(MAKE) -C extraction/chord

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

.PHONY: default quick clean lint distclean chord
