OCAMLBUILD = ocamlbuild -package verdi-runtime -I ml -I coq -cflag -g

CHORDSERIALIZEDMLFILES = coq/ExtractedChordSerialized.ml coq/ExtractedChordSerialized.mli

default: chordserialized.native client.native

$(CHORDSERIALIZEDMLFILES):
	+$(MAKE) -C ../.. extraction/chord-serialized/$@

chordserialized.native: $(CHORDSERIALIZEDMLFILES) ml/*.ml
	$(OCAMLBUILD) chordserialized.native

client.native: $(CHORDSERIALIZEDMLFILES) ml/client.ml
	$(OCAMLBUILD) client.native

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(CHORDSERIALIZEDMLFILES)

.NOTPARALLEL: chordserialized.native client.native
.NOTPARALLEL: $(CHORDSERIALIZEDMLFILES)
