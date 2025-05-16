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
RoutineTest := procedure(p, n, d : f := 1, verbose := false, check := true)
    print "Time taken to generate equations:";
    time eqs := GenTwistedVeronese(p, n, d);
    if verbose then
        printf "We have a twist of the %o-dimensional veronese variety of", n;
        printf " degree %o over the field of cardinal %o. Its equations ", d, p;
        print "are :";
        print eqs;
    end if;
    print "Time taken to compute a projective equivalence:";
    time sol := EquivalenceToVeronese(n, d, eqs : f := f, verbose := verbose);
    if check then 
        if CheckEquivalenceToVeronese(eqs, sol, n, d) then
            print "An equivalence was found.";
        else
            print "The program gave an incorrect output.";
        end if;
    end if;
end procedure;

// The same test as above, but instead of generating a twist of a Veronese
// variety and computing its Lie algebra, we only compute a twist of the Lie
// algebra of a Veronese variety.
RoutineTestLie := procedure(p, n, d : verbose := false, check := true)
    print "Time taken to generate a Lie algebra:";
    time g, natural_rep, vero_basis := GenTwistedVeroneseLieAlgebra(p, n, d);
    if verbose then
        printf "We have generated a random conjugate of the Lie algebra of";
        printf " the %o-dimensional Veronese variety of degree %o over", n, d;
        printf "the field of cardinal %o. A basis of this Lie algebra is:\n", p;
        print [b @ natural_rep : b in Basis(g)];
    end if;
    print "Time taken to compute an isomorphism of representations:";
    time sol := EquivalenceFromLie(g, natural_rep, n, d : verbose := verbose);
    if check then
        soli := sol^-1;
        Mat := MatrixLieAlgebra(BaseRing(g), NumberOfMonomials(n, d));
        s := &and[Mat!(sol * b * soli) in Codomain(natural_rep) :
            b in vero_basis];
        if s then
            print "An isomorphism of representations was computed.";
        else
            print "The program returns an incorrect output.";
        end if;
    end if;
end procedure;
