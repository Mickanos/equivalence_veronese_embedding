//Computes the Lie algebra of the Veronese embedding of degree d (with n vars).
//Note that it is a homomorphism of Lie algebras. However, we output a map
// between Matrix algebras for practical reasons.
LieAlgebraVeroneseEmbedding := function(k, n, d)
    R := PolynomialRing(k, n);
    mons := SetToSequence(MonomialsOfDegree(R, d));
    op := [[map<R -> R | p :-> R.j * Derivative(p,i)>: j in [1..n]]:
        i in [1..n]];
    Mats := [[Matrix(
        k,
        [[MonomialCoefficient(im, col) : col in mons]
            where im is mon @ op[i][j]: mon in mons]
        ): j in [1..n]]: i in [1..n]];
    Mn := MatrixAlgebra(k, n);
    Mr := MatrixAlgebra(k, #mons);
    return map< Mn -> Mr | M :-> &+[M[i,j] * Mats[i][j]: i,j in [1..n]]>, mons;
end function;

// *******************************
// ** COMPUTING THE LIE ALGEBRA **
// *******************************

// input: n x n matrices A1, ..., At
// output: The Lie algebra of square matrices X such that
// X^t*Ai + Ai*X is contained in <A1, ..., At> for all i
ComputeLieAlgebra := function(A)
  F := BaseRing(A[1]);
  n := Nrows(A[1]);
  Mat := MatrixAlgebra(F,n);
  MatAss, phi := Algebra(Mat);
  Mod := Module(MatAss);
  AMod, Quo := quo<Mod | [Mod!(a @ phi) : a in A]>;
  M := Matrix([
    &cat[Eltseq(Quo(Mod!(phi(Transpose(b)*a + a*b)))): a in A] cat
    [Trace(b)] :
    b in Basis(MatrixAlgebra(F,n))]);
  B := Basis(Kernel(M));
  MatBasis := [Matrix(F,n,n,Eltseq(b)): b in B];
  ALie := sub<MatrixLieAlgebra(F, n) | MatBasis>;
  L, phi := LieAlgebra(ALie);
  return L, Inverse(phi);
end function;

//Given quadratic equations for a projective variety, find an isomorphism
//to the Lie algebra of the Veronese embedding.
//Outputs a list of pairs of equivalent basis elements of the Lie algebras
//respectively of the given variety and of the Veronese embedding.
VeroneseLieAlgebraIsom := function(n, d, eqs)
    Quads := [QuadricToMatrix(e) : e in eqs];
    k := BaseRing(Quads[1]);
    g, natural_rep := ComputeLieAlgebra(Quads);
    g_to_sln := SplitSln(g);
    veronese_rep := LieAlgebraVeroneseEmbedding(k, n, d);
    return [<Matrix(b @ natural_rep),
        b @ (g_to_sln * veronese_rep )>: b in Basis(g)];
end function;

//Takes two isomorphic Lie algebras embedded in gl_n.
//They should be represented as one list of pairs of matrices
//corresponding to respective basis elements of each Lie algebras
//that are images of one another by a Lie algebra isomorphism.
//Outputs an isomorphism of the natural representation. That is,
//an invertible matrix T in gl_n such that the second Lie algebra is the
//conjugate of the first by T.
LieAlgebraRepresentationIsomorphism := function(pairs)
    Mat := Parent(pairs[1][1]);
    system := Matrix([&cat[Eltseq(p[1]*e - e*p[2]): p in pairs] :
        e in Basis(Mat)]);
    K := Nullspace(system);
    k := BaseRing(pairs[1][1]);
    r := NumberOfRows(pairs[1][1]);
    return [Matrix(k,r,r,Eltseq(b)) : b in Basis(K)];
end function;


//Given quadric equations for a projective variety, computes a projective
//Equivalence to the Veronese embedding of degree d with n variables.
EquivalenceToVeronese := function(n, d, eqs)
    lie_isom := VeroneseLieAlgebraIsom(n, d, eqs);
    return LieAlgebraRepresentationIsomorphism(lie_isom);
end function;