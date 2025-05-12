load "utility.m";
load "veronese_equations.m";
load "gen.m";
load "lie_algebra_isomorphism.m";
load "projective_equivalence.m";

// Generates a twist of the n-dimensional Veronese variety of degree d
// over the finite field of cardinal p. The optional parameter f is the
// proportion of the equations that are used for computing the Lie algebra
// of the variety. The choice of f has a big effect on the runtime of the
// equivalence computation. However, the optimal choice depends on the
// parameters and we only have empirical data for the moment.
RoutineTest := procedure(p, n, d : f := 1)
    print "Time to generate equations:";
    time eqs := GenTwistedVeronese(p, n, d);
    print "Time to look for a projective equivalence:";
    time sol := EquivalenceToVeronese(n, d, eqs : f := f);
    if IsEmpty(sol) then
        print "The isomorphism of Lie algebras did not yield a projective",  
        " equivalence.";
    else
        if CheckEquivalenceToVeronese(eqs, sol[1], n, d) then
            print "An equivalence was found.";
        else
            print "The program did output an incorrect solution.";
        end if;
    end if;
end procedure;