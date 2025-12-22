load "precomputed_data.m";
load "central_extension.m";
load "lie_algebra_constructions.m";
load "lie_algebra_computation.m";
load "lie_algebra_isomorphism.m";
load "veronese_representations_isomorphism.m";
load "cryptanalytical_reductions.m";
load "testing_helpers.m";

/*
    Generates public data for the scheme Vero3, recovers the obfuscated
    Veronese variety from the public data and computes a projective equivalence
    to the standard Veronese variety.
    Inputs:
        - q : The size of the base field.
        - d : The degree of the Veronese embedding used for Vero3.
*/
CryptanalysisVero3 := procedure(q, d: optimise_lie_computation := true)
    k := GF(q);
    print "Time taken to generate random public data for Vero3:";
    time pp, Sigma, M := Vero3PublicData(k, d);

    T := Cputime();
    print "Time taken to compute equations for the obfuscated threefold:";
    time eqs := VeroReduction(pp, Sigma, M);

    print "Time taken to compute the Lie algebra of the obfuscated threefold:";
    time _, rep_threefold := ComputeLieAlgebra(
        eqs:
        optimise := optimise_lie_computation,
        n := 3,
        d := d);

    printf "Time taken to recompute the Lie algebra of the Veronese threefold \
of degree %o:\n", d;
    time rep_vero := VeroneseRepresentation(k, 3, d);

    print "Time taken to recover a projective equivalence to the Veronese \
threefold:";
    time sol := VeroneseRepresentationsEquivalence(rep_threefold, rep_vero, 3, d);
    T := Cputime(T);

    if CheckEquivalenceToVeronese(eqs, sol, 3, d) then
        print "An equivalence was found.";
    else
        print "The program gave an incorrect output.";
    end if;

    printf "The total time needed for solving the problem was %o.\n", T;
end procedure;

/*
    Generates public data for the scheme Vero2, recovers the obfuscated
    Veronese variety from the public data and computes a projective equivalence
    to the standard Veronese variety.
    Inputs:
        - q : The size of the base field.
        - d : The degree of the Veronese embedding used for Vero3.
*/
CryptanalysisVero2 := procedure(q, d: optimise_lie_computation := true)
    k := GF(q);
    print "Time taken to generate random public data for Vero3:";
    time pp, Sigma, M := Vero2PublicData(k, d);

    T := Cputime();
    print "Time taken to compute equations for the obfuscated surface:";
    time eqs := VeroReduction(pp, Sigma, M);

    print "Time taken to compute the Lie algebra of the obfuscated surface:";
    time _, rep_surface := ComputeLieAlgebra(
        eqs:
        optimise := optimise_lie_computation,
        n := 2,
        d := d);

    printf "Time taken to recompute the Lie algebra of the Veronese surface of \
degree %o:\n", d;
    time rep_vero := VeroneseRepresentation(k, 2, d);

    print "Time taken to recover a projective equivalence to the Veronese \
surface:\n";
    time sol := VeroneseRepresentationsEquivalence(rep_surface , rep_vero, 2, d);
    T := Cputime(T);

    if CheckEquivalenceToVeronese(eqs, sol, 2, d) then
        print "An equivalence was found.";
    else
        print "The program gave an incorrect output.";
    end if;

    printf "The total time needed for solving the problem was %o.\n", T;
end procedure;

/*
    Generates two twists of a Veronese variety, and compute a projective equivalence between these varieties.
    Inputs:
        - q : The size of the base field.
        - n : The dimension of the Veronese varieties.
        - d : The degree of the Veronese varieties.
        - optimise_lie_computation : Flag to toggle optimisation for the Lie 
            algebra computation.
*/
RoutineTest := procedure(q, n, d : optimise_lie_computation := true)
    print "Time taken to generate equations:";
    time eqs_1 := GetTwistedVeronese(q, n, d);
    time eqs_2 := GetTwistedVeronese(q, n, d);

    timing := Cputime();
    print "Time taken to compute the Lie algebras of the varieties.";
    time _, rep1 := ComputeLieAlgebra(
        eqs_1 :
        optimise := optimise_lie_computation,
        n := n,
        d := d);
    time _, rep2 := ComputeLieAlgebra(
        eqs_2 :
        optimise := optimise_lie_computation,
        n := n,
        d := d);

    print "Time taken to compute a projective equivalence:";
    time T := VeroneseRepresentationsEquivalence(rep1, rep2, n, d);
    timing := Cputime(timing);

    if CheckProjectiveEquivalence(eqs_1, eqs_2, T) then
        print "An equivalence was found.";
    else
        print "The program gave an incorrect output.";
    end if;

    printf "In total, the time taken to solve the problem was %o.\n", timing;
end procedure;

/*
    Generates the Lie algebra representations attached to two twists of a 
    Veronese variety, and computes an isomorphism between these representations.
    This isomorphism is a projective equivalence between the underlying
    varieties.
    This tests the computation of projective equivalence without having to
    do the lengthy computation of the Lie algebra of projective varieties.
    Inputs:
        - q : The size of the base field.
        - n : The dimension of the Veronese varieties.
        - d : The degree of the Veronese varieties.
*/
RoutineTestNoLie := procedure(q, n, d)
    print "Time taken to generate Lie algebra representations:";
    time _, rep1 := GetTwistedVeroneseRepresentation(q, n, d);
    time _, rep2 := GetTwistedVeroneseRepresentation(q, n, d);

    print "Time taken to compute an isomorphism of representations:";
    time T := VeroneseRepresentationsEquivalence(rep1, rep2, n, d);
end procedure;

