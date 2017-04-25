COQVERSION := $(shell coqc --version|grep "version 8.5")

ifeq "$(COQVERSION)" ""
$(error "Verdi Chord is only compatible with Coq version 8.5")
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

CHORDMLFILES = extraction/chord/coq/ExtractedChord.ml extraction/chord/coq/ExtractedChord.mli
MLFILES = $(CHORDMLFILES)

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq -no-install \
	  -extra '$(CHORDMLFILES)' \
	    'extraction/chord/coq/ExtractChord.v systems/Chord.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/chord/coq/ExtractChord.v' \
	  -extra-phony 'distclean' 'clean' \
	    'rm -f $$(join $$(dir $$(VFILES)),$$(addprefix .,$$(notdir $$(patsubst %.v,%.aux,$$(VFILES)))))'

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq
	$(MAKE) -C extraction/chord clean

chord:
	+$(MAKE) -C extraction/chord chord.native client.native

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

.PHONY: default quick clean lint distclean chord $(MLFILES)
