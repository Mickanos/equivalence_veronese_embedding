load "utility.m";
load "gen.m";
load "lie_algebra_isomorphism.m";
load "projective_equivalence.m";

eqs := GenToyVeronese();
n := 4;
d := 2;
//sol, pairs := EquivalenceToVeronese(n, d, eqs);