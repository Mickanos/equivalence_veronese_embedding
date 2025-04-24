load "utility.m";
load "gen.m";
load "lie_algebra_isomorphism.m";

LieI := GenToyVeronese();
L, to_mat := LieAlgebra(LieI);
Lss, quo_map := quo<L | [L!b : b in Basis(Center(L))]>;
phi := SplitSln(Lss);