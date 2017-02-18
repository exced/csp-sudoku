# Constraint Satisfaction Problem - Sudoku

1. Variables: 81 in a 9x9 sudoku.
2. Domains: [1..9]
3. Constraints: Only one occurence of a number in each row, each colum and unit.

Note that we use binary constraints : there are 810 all-different binary constraints between variables.

To compile :
```bash
make
```

To run with your own sudoku :
```bash
cat >mySudoku
000070000
001284900
092301670
370060094
000000000
520040036
003402700
200896001
040030020

./sudoku <mySudoku
```

## Use Docker to work with Ocaml and its graph dependency
'''bash
make docker-run #or
docker run ocaml/opam:ubuntu-14.04_ocaml-4.02.3 opam depext -i ocamlgraph
'''

## Ocaml graph library
[Link for documentation and download](http://ocamlgraph.lri.fr)
Install :
'''bash
wget http://ocamlgraph.lri.fr/download/ocamlgraph-1.8.7.tar.gz
tar xvzf ocamlgraph-1.8.7.tar.gz
rm ocamlgraph-1.8.7.tar.gz
cd ocamlgraph-1.8.7/
./configure
make
make install
'''

## Work with Ocaml
To run the interpretor :
```bash
ledit ocaml -I /usr/local/lib/ocaml/ocamlgraph graph.cma
#use "sudoku.ml";;
```
