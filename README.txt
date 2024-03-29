InfSat version 0.1 (c) 2019 by Jan Wroblewski

License
--------
InfSat is released under the terms of the GPL version 3.0.
See the file COPYING for license terms.
InfSat is based on HorSat2 version 0.96 by Naoki Kobayashi and Taku Terao. HorSat2 is also
licensed under the GPL version 3.0.

How to install
--------------
First install and configure opam (docs on https://opam.ocaml.org/doc/Install.html), then
install OCaml 4.08.1 (docs on http://www.ocaml.org/docs/install.html#OPAM), e.g., using
opam switch create 4.08.1
and finally install opam package dependencies using
make install-dependencies

Run "make infsat" to make the final executable. Run "make run-test" to compile and run all
tests.

Run "make benchmark" to run benchmarks with all optimizations and 60s timeout and
"make infsat && bash benchmark-all.sh" to run benchmarks for all combinations of
optimization flags and 600s timeout. In the second case, new files with results will be
created in the benchmarks directory. Note that ERROR result of a benchmark usually means
stack overflow, i.e., insufficient memory.

Usage
------
To use the program:
./infsat input_file.inf

Additional options are described in:
./infsat -help

Format of Input File
--------------------
The input file should consist of grammar section and terminal definitions section. It is in the
form:

Grammar.
<rewriting rule 1>
...
<rewriting rule n>
End.

Terminals.
<terminal rule 1>
...
<terminal rule k>
End.

Comments may be placed in ocaml style (* comment *). Terminals section is optional.

Each rewriting rule should be in the form (for M >= 0):
NonterminalName arg1 ... argM -> <term>.
The first nonterminal on the list is the starting symbol.

Each terminal rule should be in the form (for arity >= 0):
terminalName -> arity [+|*] [$].
+ or * are optional and mean that nondeterministically one or all paths are taken. When + and * are
not present, + is the default. $ means that the terminal is counted. When $ is not present, the
terminal is not counted.
Note that there is a path of arbitrary length if and only if there is a tree of arbitrary size.
Therefore, the only real difference between + and * is that * can be large in one branch, and
counted in the other.

There are four reserved terminals a, b, e, t with meanings:
a -> 1 $.
b -> 2 +.
t -> 2 *.
e -> 0.
These terminals can be used without defining them and can't be redefined.

Terms are in the form
argX
terminalName
NonterminalName
(term)
term1 term2

Examples can be found in directory "examples". Larger examples can be found in directory
"benchmark".

TODO
----
* cleanup of 0CFA module and its documentation
* cleanup of conversion module by converting it to a class
* remove global state in type module (where types are assigned a unique integer and the counter
  used to generate them is still a global state)
* Possible optimizations:
  - pre-computing short-circuit-friendly order of computing argument types for type_check_app
  - computing terms without variables first and short circuit after for all terms
  - computing terms with non-duplicating variables last with short-circuiting when duplication
    is expected
  - some kind of cache for typings of hterms computed by type_check even for failed typings;
    the main problem is that the typing depends on pr var flags, context, and typing of
    nonterminals, so efficient way of checking which context is a subset of current one would
    be needed along with invalidating on nonterminal change (though this does not work well
    with optimization to force nonterminal typings)
  - early removing contexts that do not satisfy requirements when it is known a branch with
    needed loc won't be taken
  - reusing output context from previous argument instead of intersecting it in typing app
  - computing minimum mask of variables that are needed to compute type of hterms or nt to
    remove types like [T; T; ...]
  - not using types like [T; T; ...] when a type having no T is present (basic subtyping with
    only one relation T >= t for all t)
