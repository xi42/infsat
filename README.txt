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
install OCaml 4.07.1 (docs on http://www.ocaml.org/docs/install.html#OPAM), e.g., using
opam switch create 4.07.1
and finally install opam package dependencies using
make install-dependencies

Run "make infsat" to make the final executable. Run "make run-test" to compile and run all
tests.

TODO update readme later

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

Each rewriting rule should be in the form (for M >= 0):
NonterminalName arg1 ... argM -> <term>.
The first nonterminal on the list is the starting symbol.

Each terminal rule should be in the form (for arity >= 0):
terminalName -> arity.
for not counted terminals or
terminalName -> arity $.
for counted terminals. All terminals declared in such way are branching, i.e., have exactly one
argument of type different than T or are of arity 0.

Terms are in the form
argX
terminalName
NonterminalName
(term)
term1 term2
br
tr

Reserved terminals br and tr are branch and tree terminals, respectively. Branch terminal has
definition:
br -> 2.
Tree terminal is special terminal for binary tree node, i.e., the only terminal which does not
branch.

Examples can be found in directory "examples".

TODO
----
* terminals to a -> <children> [counted] <universal/existential (optional if children <= 1>.
* grammars to test displaying proofs when escape path crosses path to cycle - counting number of gathered proofs
* check TODOs in code and resolve them or move here
* types of variables will be displayed directly, not as not-productive - is this a problem?
* benchmark on horsat tests
* update documentation
