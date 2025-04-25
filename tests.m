load "main.m";

TestSplitSln := procedure()
    eqs := GenVeronese(NextPrime(2^20), 2, 2);
    Quads := [QuadricToMatrix(e) : e in eqs];
    Lie := ComputeLieAlgebra(Quads);
    g := quo < Lie | Basis(Center(Lie))>;
    g_to_mat := SplitSln(g);
    assert IsLieHom(g_to_mat, Basis(g));
    Im := Matrix([Eltseq(b @ g_to_mat): b in Basis(g)]);
    assert Rank(Im) eq Dimension(g);
end procedure;

TestSplitSlnSplitCartan := procedure()
    eqs := GenVeronese(NextPrime(2^20), 2, 2);
    Quads := [QuadricToMatrix(e) : e in eqs];
    Lie := ComputeLieAlgebra(Quads);
    g := quo < Lie | Basis(Center(Lie))>;
    _, gK := BaseChangeAndSplitCartan(g);
    g_to_mat := SplitSln(gK);
    assert IsLieHom(g_to_mat, Basis(gK));
    Im := Matrix([Eltseq(b @ g_to_mat): b in Basis(gK)]);
    assert Rank(Im) eq Dimension(gK);
end procedure;

TestLieAlgebraVeroneseEmbedding := procedure()
    k := GF(101);
    n := 4;
    d := 2;
    e := LieAlgebraVeroneseEmbedding(k, n, d);
    assert IsLieHom(e, Basis(Domain(e)));
    Im := Matrix([Eltseq(b @ e): b in Basis(Domain(e))]);
    assert Rank(Im) eq 16;
end procedure;

TestVeroneseLieAlgebraIsom := procedure()
    n := 4;
    d := 2;
    eqs := GenVeronese(NextPrime(2^20), d, 2);
    pairs := VeroneseLieAlgebraIsom(n, d, eqs);
    k := BaseRing(pairs[1][1]);
    gl := MatrixLieAlgebra(k, 10);
    A := sub<gl | [p[1] : p in pairs]>;
    L, phi := LieAlgebra(A);
    B := sub<gl | [p[2] : p in pairs]>;
    M, psi := LieAlgebra(B);
    L := ChangeBasis(L, [p[1] @ phi : p in pairs]);
    iso := hom<L -> M | [p[2] @ psi : p in pairs]>;
    assert IsIsomorphism(iso);
end procedure;

TestEquivalenceToVeronese := procedure()
    n := 4;
    d := 2;
    repeat 
        eqs := GenVeronese(NextPrime(2^20), d, 2);
        sol := EquivalenceToVeronese(n, d, eqs);
    until #sol eq 1;
    k := BaseRing(sol[1]);
    T := sol[1];
    veqs := VeroneseEquations(k, n, d);
    assert CheckProjectiveEquivalence(eqs, veqs, T);
end procedure;

TestSplitSln();
TestSplitSlnSplitCartan();
TestLieAlgebraVeroneseEmbedding();
TestVeroneseLieAlgebraIsom();
TestEquivalenceToVeronese();