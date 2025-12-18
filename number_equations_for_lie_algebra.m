load "main.m";

//Checking our heuristic optimisation for the bottleneck of the  computation
// of the Lie algebra.
// Checks how often taking a fraction s of the equations of a random variety
// oisomorphic to the Veronese variety allows to compute the Lie algebra
/*
    Estimates the frequency at which the computation of the Lie algebra of
    a twisted Veronese variety succeeds if only a random subset of given size
    of its equations is used.
    Inputs:
        - q: The size of the base field.
        - n: The dimension of the Veronese variety.
        - d: The degree of the Veronese variety.
        - f: The proportion of equations used in the computation.
        - reps: The number of datapoints generated for the estimation.
*/
SuccessFrequency := function(q, n, d, f : reps := 100)
    successes := 0;
    timing := 0;
    for count in [1..reps] do
        eqs := GetTwistedVeronese(q, n, d);
        eqs := [SymmetricMatrix(e) : e in eqs];
        k := GF(q);
        N := Nrows(eqs[1]);
        number_eqs_used := Ceiling(f * #eqs);
        MS := KMatrixSpace(k, N, N);
        AMod, Quo := quo<MS | eqs>;
        T := Cputime();

        used_eqs := RandomElements(eqs, number_eqs_used);
        M := HorizontalJoin([Matrix([Eltseq(Quo(Transpose(b)*a + a*b)) :
            b in Basis(MS)]): a in used_eqs]);
        M := Transpose(M);
        RemoveZeroRows(~M);
        M := Transpose(M);
        ker := Nullspace(M);

        timing +:= Cputime(T);
        if Dimension(ker) eq (n + 1)^2 then
            successes +:= 1;
        end if;
    end for;
    return successes/reps, timing/reps;
end function;

/*
    Runs the computation of the success frequency of the Lie algebra computation
    for a range of parameters.
    Inputs:
        - q: The size of the base field.
        - n: The dimension of the Veronese variety.
        - d: The degree of the Veronese variety.
        - min: The smallest value of the tested parameter f.
        - step: The step between the various choices of f.
        - n_steps: The number of values test for f.
        - reps: The number of data points used for each estimation.
*/
TransversalTest := procedure(q, n, d, min, step, n_steps : reps := 100)
    f := min;
    for _ in [1..n_steps] do
        succ, tim := SuccessFrequency(q, n, d, f : reps := reps);
        print Sprintf("For %o variables and degree %o, taking only", n, d) cat
            Sprintf(" a fraction %o of equations yields a %o rate", f, succ) cat
            Sprintf(" of success. Computing the Lie algebra takes %o", tim) cat
            " seconds on average.";
        f +:= step;
    end for;
end procedure; 