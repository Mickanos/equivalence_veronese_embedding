load "utility.m";
load "veronese_equations.m";
load "gen.m";
load "central_extension.m";
load "lie_algebra_isomorphism.m";
load "projective_equivalence.m";

// Generates a twist of the n-dimensional Veronese variety of degree d
// over the finite field of cardinal p. The optional parameter f is the
// proportion of the equations that are used for computing the Lie algebra
// of the variety. The choice of f has a big effect on the runtime of the
// equivalence computation. However, the optimal choice depends on the
// parameters and we only have empirical data for the moment.
RoutineTest := procedure(p, n, d : f := 1, verbose := false, check := true)
    print "Time taken to generate equations:";
    time eqs_1 := GenTwistedVeronese(p, n + 1, d);
    time eqs_2 := GenTwistedVeronese(p, n + 1, d);
    if verbose then
        printf "We have two twists of the %o-dimensional veronese variety of", n;
        printf " degree %o over the field of cardinal %o. Their equations ", d, p;
        print "are :";
        print eqs_1;
        print eqs_2;
    end if;
    print "Time taken to compute a projective equivalence:";
    time sol := ComputeProjectiveEquivalence(eqs_1, eqs_2, n + 1);
    if check then 
        if CheckProjectiveEquivalence(eqs_1, eqs_2, sol) then
            print "An equivalence was found.";
        else
            print "The program gave an incorrect output.";
        end if;
    end if;
end procedure;