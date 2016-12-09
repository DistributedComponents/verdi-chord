OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -I coq

MLFILES = coq/ExtractedChord.ml coq/ExtractedChord.mli \
	coq/ExtractedChordShed.ml coq/ExtractedChordShed.mli

default: chord.native client.native chordshed.native

$(MLFILES):
	+$(MAKE) -C ../.. extraction/chord/$@

chord.native: coq/ExtractedChord.ml ml/*.ml lib/*.ml
	$(OCAMLBUILD) chord.native

client.native: ml/client.ml coq/ExtractedChord.ml lib/*.ml
	$(OCAMLBUILD) client.native

chordshed.native: coq/ExtractedChordShed.ml ml/*.ml lib/*.ml
	$(OCAMLBUILD) chordshed.native

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(MLFILES)

.NOTPARALLEL: chord.native client.native chordshed.native
.NOTPARALLEL: $(MLFILES)
