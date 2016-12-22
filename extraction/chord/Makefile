OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -I coq

CHORDMLFILES = coq/ExtractedChord.ml coq/ExtractedChord.mli
SHEDMLFILES = coq/ExtractedChordShed.ml coq/ExtractedChordShed.mli

default: chord.native client.native chordshed.native

$(CHORDMLFILES):
	+$(MAKE) -C ../.. extraction/chord/$@

$(SHEDMLFILES):
	+$(MAKE) -C ../.. extraction/chord/$@

chord.native: $(CHORDMLFILES) lib/*.ml
	$(OCAMLBUILD) chord.native

client.native: ml/client.ml coq/ExtractedChord.ml lib/*.ml
	$(OCAMLBUILD) client.native

chordshed.native: $(SHEDMLFILES) ml/*.ml lib/*.ml
	$(OCAMLBUILD) chordshed.native

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(MLFILES)

.NOTPARALLEL: chord.native client.native chordshed.native
.NOTPARALLEL: $(MLFILES)
