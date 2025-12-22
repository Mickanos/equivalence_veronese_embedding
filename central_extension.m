/*****************************************************************
*                      Central Extensions                        *
*****************************************************************/

/*
    Computing central extensions of Lie algebras using cohomology.
    See Section 7.6 of Charles A. Weibel's An introduction to homological
    algebra for theoretical details.
*/

forward NontrivialCohomologyClass;
/*
    Computes a nontrivial central extension of the Lie algebra g,
    if such an extension exists.
    Inputs:
        - g : The Lie algebra to extend.
*/
NontrivialCentralExtension := function(g)
    f := NontrivialCohomologyClass(g);
    d := Dimension(g) + 1;
    k := BaseRing(g);
    Q := [[[0: _ in [1..d]]: _ in [1..d]]]
        cat [
            [[0: _ in [1..d]]]
            cat [
                [f(a, b)] cat Eltseq(BasisProduct(g, i, j))
            : j -> b in Basis(g)
            ]
        : i -> a in Basis(g)
        ];
    e := LieAlgebra<k, d | Q>;
    lift := hom<g -> e | Basis(e)[2..d]>;
    proj := hom<e -> g | [Zero(g)] cat Basis(g)>;
    return e, lift, proj;
end function;

/*
    Computes the direct sum of a Lie algebra with an Abelian Lie algebra of
    dimension 1.
    inputs:
        - g: The Lie algebra.
*/
TrivialCentralExtension := function(g)
    k := BaseRing(g);
    d := Dimension(g);
    e := DirectSum(AbelianLieAlgebra(k, 1), g);
    lift := hom<g -> e | Basis(e)[2..d + 1]>;
    proj := hom<e -> g | [Zero(g)] cat Basis(g)>;
    return e, lift, proj;
end function;

/*
    Computes a basis of the space of antisymmetric matrices.
    Inputs:
        - k: The base field of the matrices.
        - n: The size of the matrices.
*/
AntisymmetricMatricesBasis := function(k, n)
    N := Binomial(n, 2);
    return [AntisymmetricMatrix([Zero(k):
        _ in [1..i-1]] cat [One(k)] cat [Zero(k): _ in [i+1..N]]): i in [1..N]];
end function;

/*
    Computes a basis of the vector space of 2-cocycles of a Lie algebra
    with coefficients in the trivial module of dimension 1.
    Inputs:
        - g: The Lie algebra whose cohomology is computed.
*/
TwoCocycles := function(g)
    k := BaseRing(g);
    n := Dimension(g);
    antisym := AntisymmetricMatricesBasis(k, n);
    system := Matrix([
        [
            (Vector(g1) * A, Vector(g2 * g3)) +
            (Vector(g2) * A, Vector(g3 * g1)) +
            (Vector(g3) * A, Vector(g1 * g2))
        : g1, g2, g3 in Basis(g)]
    : A in antisym]);
    return Nullspace(system);
end function;

/*
    Computes a basis of the vector space of 2-coboundaries of a Lie algebra
    with coefficients in the trivial module of dimension 1.
    Inputs:
        - g: The Lie algebra whose cohomology is computed.
*/
TwoCoboundaries := function(g)
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

/*
    Computes a 2-cocycle that is not a 2-coboundary.
    Inputs:
        - g: The Lie algebra whose cohomology is computed.
*/
NontrivialCohomologyClass := function(g)
    z2 := TwoCocycles(g);
    b2 := TwoCoboundaries(g);
    v := Basis(Complement(z2, b2))[1];
    A := AntisymmetricMatrix(Eltseq(v));
    return map<CartesianPower(g, 2) -> BaseRing(g) |
        t :-> (Vector(t[1]) * A, Vector(t[2]))>;
end function;