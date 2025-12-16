load "lie_algebra_constructions.m";
load "lie_algebra_computation.m";
load "central_extension.m";
load "lie_algebra_isomorphism.m";
load "projective_equivalence.m";
load "testing_helpers.m";
load "veronese_equations.m";

// Generates a twist of the n-dimensional Veronese variety of degree d
// over the finite field of cardinal p. The optional parameter f is the
// proportion of the equations that are used for computing the Lie algebra
// of the variety. The choice of f has a big effect on the runtime of the
// equivalence computation. However, the optimal choice depends on the
// parameters and we only have empirical data for the moment.
RoutineTest := procedure(p, n, d)
    print "Time taken to generate equations:";
    time eqs_1 := GetTwistedVeronese(p, n + 1, d);
    time eqs_2 := GetTwistedVeronese(p, n + 1, d);

    print "Time taken to compute the Lie algebras of the varieties.";
    time _, rep1 := ComputeLieAlgebra(eqs_1);
    time _, rep2 := ComputeLieAlgebra(eqs_2);

    print "Time taken to compute a projective equivalence:";
    time sol := VeroneseRepresentationsEquivalence(rep1, rep2, n + 1, d);

    if CheckProjectiveEquivalence(eqs_1, eqs_2, sol) then
        print "An equivalence was found.";
    else
        print "The program gave an incorrect output.";
    end if;
end procedure;

RoutineTestNoLie := procedure(p, n, d)
    print "Time taken to generate Lie algebra representations:";
    time _, rep1 := GetTwistedVeroneseRepresentation(p, n + 1, d);
    time _, rep2 := GetTwistedVeroneseRepresentation(p, n + 1, d);

    print "Time taken to compute an isomorphism of representations:";
    time sol := VeroneseRepresentationsEquivalence(rep1, rep2, n + 1, d);
end procedure;