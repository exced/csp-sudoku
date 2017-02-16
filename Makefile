
TARGET=sudoku

all: $(TARGET)

$(TARGET):
	ocamlopt -I /usr/local/lib/ocaml/ocamlgraph -o sudoku graph.cmxa sudoku.ml

run:
	./sudoku <example

runtime:
	time ./sudoku <example 		

clean:
	rm -f sudoku.cmi
	rm -f sudoku.cmx
	rm -f sudoku.o
	rm -f sudoku
