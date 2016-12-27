OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -I coq

CHORDMLFILES = coq/ExtractedChord.ml coq/ExtractedChord.mli
SHEDMLFILES = coq/ExtractedChordShed.ml coq/ExtractedChordShed.mli

default: chord.native client.native chordshed.native

$(CHORDMLFILES) $(SHEDMLFILES):
	+$(MAKE) -C ../.. extraction/chord/$@

chord.native: $(CHORDMLFILES) ml/*.ml lib/*.ml
	$(OCAMLBUILD) chord.native

client.native: $(CHORDMLFILES) ml/client.ml lib/*.ml
	$(OCAMLBUILD) client.native

chordshed.native: $(SHEDMLFILES) ml/*.ml lib/*.ml
	$(OCAMLBUILD) chordshed.native

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(CHORDMLFILES) $(SHEDMLFILES)

.NOTPARALLEL: chord.native client.native chordshed.native
.NOTPARALLEL: $(CHORDMLFILES) $(SHEDMLFILES)
