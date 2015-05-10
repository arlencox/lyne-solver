all:
	ocamlbuild -package unix -package str encode.d.byte

clean:
	ocamlbuild -clean
