load "gen.m";
success_frequency := function(p, n, d, s : reps := 100)
    successes := 0;
    for _ in [1..reps] do
        eqs := GenTwistedVeronese(p, n, d);
        A := [QuadricToMatrix(e) : e in eqs];
        F := GaloisField(p);
        n := Nrows(A[1]);
        AMod, Quo := quo<KMatrixSpace(F, n, n) | A>;
        sA := RandomElements(A, s);
        M := HorizontalJoin(
            HorizontalJoin([Matrix([Eltseq(Quo(Transpose(b)*a + a*b)) :
            b in Basis(MatrixAlgebra(F,n))]): a in sA]),
            Matrix(F, n^2, 1, [Trace(b) : b in Basis(MatrixAlgebra(F,n))]));
        M := Transpose(M);
        RemoveZeroRows(~M);
        M := Transpose(M);
        B := Basis(Nullspace(M));
        if #B eq n^2 - 1 then
            successes +:= 1;
        end if;
    end for;
    return successes/reps;
end function;