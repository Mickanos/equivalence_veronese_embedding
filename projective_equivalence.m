//Computes the Lie algebra of the Veronese embedding of degree d (with n vars).
//Note that it is a homomorphism of Lie algebras. However, we output a map
// between Matrix algebras for practical reasons.
LieAlgebraVeroneseEmbedding := function(k, n, d)
    R := PolynomialRing(k, n);
    mons := SetToSequence(MonomialsOfDegree(R, d));
    op := [[map<R -> R | p :-> R.i * Derivative(p,j)>: j in [1..n]]:
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
        &cat[Eltseq(Quo(Mod!(phi(Transpose(b)*a + a*b)))): a in A]
    : b in Basis(MatrixAlgebra(F,n))]);
  B := Basis(Kernel(M));
  MatBasis := [Matrix(F,n,n,Eltseq(b)): b in B];
  MatLie := MatrixLieAlgebra(F,n);
  return sub<MatLie | MatBasis>;
end function;

//Given quadric equations for a projective variety, computes a projective
//Equivalence to the Veronese embedding of degree d with n variables.
EquivalenceToVeronese := function(n, d, eqs)
    Quads := [QuadricToMatrix(e) : e in eqs];
    k := BaseRing(Quads[1]);
    Lie, mat_to_lie := ComputeLieAlgebra(Quads);
    g, lie_to_g := quo < Lie | Basis(Center(Lie)) >;
    g_to_mat := SplitSln(g);
    small_mat_to_big_mat := LieAlgebraVeroneseEmbedding(k, n, d);
    pairs := [<b @@ (mat_to_lie * lie_to_g),
        b @ (g_to_mat * small_mat_to_big_mat)>: b in Basis(g)];
end function;