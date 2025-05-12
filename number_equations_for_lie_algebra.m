load "utility.m";
load "veronese_equations.m";
load "gen.m";
success_frequency := function(p, N, d, s : reps := 100)
    successes := 0;
    timing := 0;
    for count in [1..reps] do
        eqs := GenTwistedVeronese(p, N, d);
        A := [QuadricToMatrix(e) : e in eqs];
        F := GaloisField(p);
        n := Nrows(A[1]);
        n_eqs := Ceiling(s * #eqs);
        AMod, Quo := quo<KMatrixSpace(F, n, n) | A>;
        T := Cputime();
        sA := RandomElements(A, n_eqs);
        M := HorizontalJoin(
            HorizontalJoin([Matrix([Eltseq(Quo(Transpose(b)*a + a*b)) :
            b in Basis(MatrixAlgebra(F,n))]): a in sA]),
            Matrix(F, n^2, 1, [Trace(b) : b in Basis(MatrixAlgebra(F,n))]));
        M := Transpose(M);
        RemoveZeroRows(~M);
        M := Transpose(M);
        B := Basis(Nullspace(M));
        timing +:= Cputime(T);
        if #B eq N^2 - 1 then
            successes +:= 1;
        end if;
    end for;
    return successes/reps, timing/reps;
end function;

transversal_test := procedure(p, n, d, min, step, n_steps : reps := 100)
    f := min;
    for _ in [1..n_steps] do
        succ, tim := success_frequency(p, n, d, f : reps := reps);
        print Sprintf("For %o variables and degree %o, taking only", n, d) cat
            Sprintf(" a fraction %o of equations yields a %o rate", f, succ) cat
            Sprintf(" of success. Computing the matrix takes %o", tim) cat
            " seconds on average.";
        f +:= step;
    end for;
end procedure; 