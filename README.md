Lyne Puzzle Solver
==================

This is a relatively simple solver for puzzles in the game
[Lyne](http://www.lynegame.com).  It translates input that resembles the puzzle
input into an SMT formula and solves it with
[Z3](https://github.com/Z3Prover/z3).  It processes the output from Z3 to give a pretty readable version of the output.

One special aspect of this encoding is that it does not utilize quantifiers.
However, as a result, the encoding is fairly large and Z3 is slow to solve it.
It has not been optimized as this is a one-day, for-fun programming challenge.


Input
-----

The input consists of a text file describing the matrix for the puzzle.  Each
cell of the matrix can be one of four elements:

  1. Empty (space character).  This cell cannot be used to complete the puzzle.
  2. Terminal (capital letter).  This cell must start or end a path
     corresponding to the lower-case version of the letter.
  3. Path Marker (lower-case letter).  This cell must be passed through only on
     the certain type of path and must only be passed through once.
  4. Numbered (single digit).  This cell must be passed through by the
     indicated number of paths.


Output
-----

The output consists of three diagrams and two files.

The first diagram shows the input puzzle.

The second diagram shows the input puzzle with each edge labeled with the path
symbol that is using it.  Usually this is sufficient to solve the puzzle.

The third diagram shows step-by-step solutions to each path.  This consists of
a list of edges that are followed in (row,column) form.

The first file is called problem.smt2 and contains the SMT encoding of the problem.

The second file is call result.smt2 and contains the output from the SMT solver.

Usage
-----

Compile the program using the included makefile (OCaml and OCamlFind required).
Solve a problem contained in `problem.txt` in the following way:

```
./encode.d.byte < problem.txt
```

Example
-------



```
$ cat inputs/inp_c24.txt
ssT
s32
2S2
StT
$ ./encode.d.byte < inputs/inp_c24.txt 
ssT
s32
2S2
StT
======================
s-s-s   T
 \   \  |
  s   s t
   \   \|
s-s-3-s-2
|  /|\  |
s t s t t
|/  |  \|
2   S   2
|\     /|
s t   t t
|  \ /  |
S   t   T
======================
2,1 -> 1,1 : s 0
1,1 -> 0,0 : s 1
0,0 -> 0,1 : s 2
0,1 -> 1,2 : s 3
1,2 -> 1,1 : s 4
1,1 -> 1,0 : s 5
1,0 -> 2,0 : s 6
2,0 -> 3,0 : s 7
0,2 -> 1,2 : t 0
1,2 -> 2,2 : t 1
2,2 -> 3,1 : t 2
3,1 -> 2,0 : t 3
2,0 -> 1,1 : t 4
1,1 -> 2,2 : t 5
2,2 -> 3,2 : t 6

```
