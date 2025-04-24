load "main.m";
load "test_utils.m";
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

TestSplitSln();
TestSplitSlnSplitCartan();
TestLieAlgebraVeroneseEmbedding();