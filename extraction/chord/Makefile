OCAMLBUILD = ocamlbuild -lib str -lib unix -I lib -I ml -I coq

default: chord.native client.native chordshed.native

coq/ExtractedChord.ml:
	make -C ../.. extraction/chord/coq/ExtractedChord.ml

coq/ExtractedChordShed.ml:
	make -C ../.. extraction/chord/coq/ExtractedChordShed.ml

chord.native: coq/ExtractedChord.ml ml/*.ml lib/*.ml
	$(OCAMLBUILD) chord.native

client.native: ml/client.ml coq/ExtractedChord.ml lib/*.ml
	$(OCAMLBUILD) client.native

chordshed.native: coq/ExtractedChordShed.ml ml/*.ml lib/*.ml
	$(OCAMLBUILD) chordshed.native

clean:
	$(OCAMLBUILD) chord.native -clean

.PHONY : default clean
