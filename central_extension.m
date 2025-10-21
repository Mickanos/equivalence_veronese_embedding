antisym_matrices := function(k, n)
    N := Binomial(n, 2);
    return [AntisymmetricMatrix([Zero(k): _ in [1..i-1]] cat [One(k)] cat [Zero(k): _ in [i+1..N]]): i in [1..N]];
end function;

two_cocycles := function(g)
    k := BaseRing(g);
    n := Dimension(g);
    antisym := antisym_matrices(k, n);
    system := Matrix([[(Vector(g1) * A, Vector(g2 * g3)) + (Vector(g2) * A, Vector(g3 * g1)) + (Vector(g3) * A, Vector(g1 * g2)): g1, g2, g3 in Basis(g)] : A in antisym]);
    return Nullspace(system);
end function;

two_coboundaries := function(g)
    k := BaseRing(g);
    n := Dimension(g);
    N := Binomial(n, 2);
    V := VectorSpace(k, N);
    return sub< V | [
        Vector([
            (Vector(d), Vector(g1 * g2)) where g2 is Basis(g)[j]
        : j in [1..i-1], i -> g1 in Basis(g)])
    : d in Basis(g)]>;
end function;

nontrivial_cohomology_class := function(g)
    z2 := two_cocycles(g);
    b2 := two_coboundaries(g);
    v := Basis(Complement(z2, b2))[1];
    A := AntisymmetricMatrix(Eltseq(v));
    return map<CartesianPower(g, 2) -> BaseRing(g) | t :-> (Vector(t[1]) * A, Vector(t[2]))>;
end function;

nontrivial_central_extension := function(g)
    f := nontrivial_cohomology_class(g);
    d := Dimension(g) + 1;
    k := BaseRing(g);
    Q := [
            [
                Eltseq(BasisProduct(g, i, j)) cat [f(a,b)]
            : j -> b in Basis(g)]
            cat [[0: _ in [1..d]]]
        : i -> a in Basis(g)]
        cat [[[0: _ in [1..d]]: _ in [1..d]]];
    e := LieAlgebra<k, d | Q>;
    lift := hom<g -> e | Basis(e)[1..d-1]>;
    return e, lift;
end function;