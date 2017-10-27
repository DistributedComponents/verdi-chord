include Makefile.detect-coq-version

ifeq (,$(filter $(COQVERSION),8.6 8.7 trunk))
$(error "Verdi Chord is only compatible with Coq version 8.6.1")
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

MLFILES = extraction/chord/coq/ExtractedChord.ml extraction/chord/coq/ExtractedChord.mli

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

proofalytics:
	$(MAKE) -C proofalytics clean
	$(MAKE) -C proofalytics
	$(MAKE) -C proofalytics publish

STDBUF=$(shell [ -x "$$(which gstdbuf)" ] && echo "gstdbuf" || echo "stdbuf")
BUILDTIMER=$(PWD)/proofalytics/build-timer.sh $(STDBUF) -i0 -o0

proofalytics-aux: Makefile.coq
	$(MAKE) -f Makefile.coq TIMECMD="$(BUILDTIMER)"

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq -install none \
	  -extra '$(MLFILES)' \
	    'extraction/chord/coq/ExtractChord.v systems/chord/Chord.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/chord/coq/ExtractChord.v'

clean:
	if [ -f Makefile.coq ]; then \
	  $(MAKE) -f Makefile.coq cleanall; fi
	rm -f Makefile.coq
	$(MAKE) -C extraction/chord clean
	$(MAKE) -C proofalytics clean

chord:
	+$(MAKE) -C extraction/chord chord.native client.native

$(MLFILES): Makefile.coq
	$(MAKE) -f Makefile.coq $@

lint:
	@echo "Possible use of hypothesis names:"
	find . -name '*.v' -exec grep -Hn 'H[0-9][0-9]*' {} \;

distclean: clean
	rm -f _CoqProject

.PHONY: default quick clean lint distclean chord $(MLFILES) proofalytics proofalytics-aux
