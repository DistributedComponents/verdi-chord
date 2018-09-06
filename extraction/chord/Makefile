OCAMLBUILD = ocamlbuild -package verdi-runtime -package yojson -I ml -I coq -cflag -g

CHORDMLFILES = coq/ExtractedChord.ml coq/ExtractedChord.mli

default: chord.native client.native

$(CHORDMLFILES):
	+$(MAKE) -C ../.. extraction/chord/$@

chord.native: $(CHORDMLFILES) ml/*.ml
	$(OCAMLBUILD) chord.native

client.native: $(CHORDMLFILES) ml/client.ml
	$(OCAMLBUILD) client.native

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(CHORDMLFILES)

.NOTPARALLEL: chord.native client.native
.NOTPARALLEL: $(CHORDMLFILES)
