eval `opam config env`

coqc Base.v
coqc Grammar.v
coqc DFA.v
coqc Intersection.v
