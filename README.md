# Constraint Satisfaction Problem - Sudoku

1. Variables: 81 in a 9x9 sudoku.
2. Domains: [1..9]
3. Constraints: Only one occurence of a number in each row, each colum and unit.

Note that we use binary constraints : there are 810 all-different binary constraints between variables.

To compile :
```bash
make
```

To run with a sudoku :
```bash
./sudoku <example
```

## Work with Ocaml
To run the interpretor :
```bash
ledit ocaml -I /usr/local/lib/ocaml/ocamlgraph graph.cma
#use "sudoku.ml";;
```
