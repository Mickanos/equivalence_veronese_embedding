load "main.m";

TestPrepareGlnQuotient := procedure()
    k := GF(101);
    n := 3;
    g, proj, graph, ConjugationDefect, lift := PrepareGlnQuotient(k, n);
    assert &and[a @ lift @ proj eq a : a in Basis(g)];
    assert IsIsomorphism(graph);
    assert &and[a @ graph eq (-Transpose(Matrix(a @ lift))) @ proj: a in Basis(g)];
    gln := Domain(proj);
    repeat
        P := Matrix(k, n, n, [Random(k) : _ in [1..n^2]]);
    until IsUnit(P);
    A := [g![Random(k) : _ in [1..Dimension(g)]] : _ in [1..Dimension(g)]];
    MA := MatrixAlgebra(k, n);
    system := Matrix([&cat[Eltseq(ConjugationDefect(
                a,
                (P * Matrix(a @ lift) * P^-1) @ proj,
                Q))
            : a in A]
        : Q in Basis(MA)]);
    assert IsZero(Vector(P) * system);
end procedure;

TestPrepareGlnQuotient();