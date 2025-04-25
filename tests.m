load "main.m";

TestSplitSln := procedure()
    eqs := GenToyVeronese();
    n := 4;
    d := 2;
    Quads := [QuadricToMatrix(e) : e in eqs];
    Lie := ComputeLieAlgebra(Quads);
    g := quo < Lie | Basis(Center(Lie))>;
    g_to_mat := SplitSln(g);
    assert IsLieHom(g_to_mat, Basis(g));
    Im := Matrix([Vector(Eltseq(b @ g_to_mat)): b in Basis(g)]);
    assert Rank(Im) eq Dimension(g);
end procedure;

TestSplitSlnSplitCartan := procedure()
    eqs := GenToyVeronese();
    n := 4;
    d := 2;
    Quads := [QuadricToMatrix(e) : e in eqs];
    Lie := ComputeLieAlgebra(Quads);
    g := quo < Lie | Basis(Center(Lie))>;
    _, gK := BaseChangeAndSplitCartan(g);
    g_to_mat := SplitSln(gK);
    assert IsLieHom(g_to_mat, Basis(gK));
    Im := Matrix([Vector(Eltseq(b @ g_to_mat)): b in Basis(gK)]);
    assert Rank(Im) eq Dimension(gK);
end procedure;

TestLieAlgebraVeroneseEmbedding := procedure()
    k := GF(101);
    n := 4;
    d := 2;
    e := LieAlgebraVeroneseEmbedding(k, n, d);
    assert IsLieHom(e, Basis(Domain(e)));
end procedure;

TestEquivalenceToVeronese := procedure()
    eqs := GenToyVeronese();
    n := 4;
    d := 2;
    sol, pairs := EquivalenceToVeronese(n, d, eqs);
    assert #sol gt 0;
    k := BaseRing(pairs[1][1]);
    gl := MatrixLieAlgebra(k, 10);
    A := sub<gl | [p[1] : p in pairs]>;
    L, phi := LieAlgebra(A);
    B := sub<gl | [p[2] : p in pairs]>;
    M, psi := LieAlgebra(B);
    L := ChangeBasis(L, [p[1] @ phi : p in pairs]);
    iso := hom<L -> M | [p[2] @ psi : p in pairs]>;
    assert IsIsomorphism(iso);
    T := Matrix(k, 10, 10, Eltseq(sol[1]));
    iT := T^-1;
    assert &and[T * p[1] * iT eq p[2] : p in pairs];
end procedure;

TestSplitSln();
TestSplitSlnSplitCartan();
TestLieAlgebraVeroneseEmbedding();
TestEquivalenceToVeronese();