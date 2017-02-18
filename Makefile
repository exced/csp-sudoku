
TARGET=sudoku

all: $(TARGET)

$(TARGET):
	ocamlopt -I /usr/local/lib/ocaml/ocamlgraph -o sudoku graph.cmxa sudoku.ml

run:
	./sudoku <example

runtime:
	time ./sudoku <example 		

docker-run:	
	docker run ocaml/opam:ubuntu-14.04_ocaml-4.02.3 opam depext -i ocamlgraph

clean:
	rm -f sudoku.cmi
	rm -f sudoku.cmx
	rm -f sudoku.o
	rm -f sudoku