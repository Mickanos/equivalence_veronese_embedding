//Returns scalar t such that t*a eq b;
//Throws an error if a and b aren't colinear vectors.
Colinearity := function(a, b)
  i := Index([IsZero(c) : c in Eltseq(a)], false);
  t := b[i]/a[i];
  assert t*a eq b;
  return t;
end function;

ElementaryMatrix := function(k, m, n, i, j)
  return Matrix(k, [[s eq i and t eq j select 1 else 0 : t in [1..n]]:
    s in [1..m]]);
end function;

//Input: a field k and a matrix M with coefficients in an extension K/k.
//Output: a matrix with coefficients in k, representing the same map as k-linear
//instead of K-linear. The basis of K as an extension of k is used to produce
//a k-basis of the domain and codomain of M.
MatrixRestrictionOfScalars := function(k, M)
    K := BaseRing(M);
    Rows := [b*r : b in Basis(K, k), r in Rows(M)];
    LongRows := [&cat[Eltseq(c, k): c in Eltseq(r)]: r in Rows];
    return Matrix(LongRows);
end function;

SplitMatrixAlgebra := function(A)
  _, n := IsSquare(Dimension(A));
  k := BaseField(A);
  MAlg := MatrixAlgebra(k, n);
  MAss, phi := Algebra(MAlg);
  I := MinimalRightIdeals(A : Limit := 1)[1];
  Mats := [Matrix([e*a: e in Basis(I)]): a in Basis(A)];
  return hom<A -> MAss | [M @ phi: M in Mats]> * Inverse(phi);
end function;

Prod := function(a,b)
    return a * b;
end function;

//Magma's LieBracket function does not work for matrices.
MyLieBracket := function(a,b)
    return a*b - b*a;
end function;

//Test if f is a homomorphism of Lie algebras.
//Works whether the domains and codomains of f are Lie algebras or
//Associative algebras.
IsLieHom := function(f, L)
    brack_dom := IsAssociative(Domain(f)) select MyLieBracket else Prod;
    brack_co := IsAssociative(Codomain(f)) select MyLieBracket else Prod;
    res := [<a,b> : a, b in L | brack_dom(a,b) @ f ne brack_co(a @ f, b @ f)];
    return IsEmpty(res), res;
end function;

//p is a polynomial in n variables and M is a square matrix of order n.
//Computes the polynomial obtained from p by linear transformation of the
//variables.
PolySubstitution := function(p, M)
  R := Parent(p);
  n := Rank(R);
  return Evaluate(p, [&+[r[i]*R.i : i in [1..n]]: r in Rows(M)]);
end function;

NumberOfMonomials := function(n, d)
  return Binomial(n+d-1, d);
end function;

//Takes a list of homogeneous polynomials of equal degrees.
//Returns a basis of the space of polynomials spanned by elements of the list.
FreeHomogeneousPolys := function(L)
  i := 1;
  repeat
    d := Degree(L[i]);
    i +:= 1;
  until d ne -1;
  R := Parent(L[1]);
  mons := SetToSequence(MonomialsOfDegree(R, d));
  vectors := [Vector([MonomialCoefficient(P, m) : m in mons]): P in L];
  space := sub<Parent(vectors[1]) | vectors>;
  return [&+[v[i]*m : i->m in mons]: v in Basis(space)];
end function;

//Generates the quadratic equations for the Veronese embedding
//Not very efficient, could probably be improved.
VeroneseEquations := function(n, d)
  Z := IntegerRing();
  R := PolynomialRing(Z, n);
  mons := SetToSequence(MonomialsOfDegree(R, d));
  S := PolynomialRing(Z, #mons);
  mon_index := map< R -> { 1..#mons } | p :-> Index(mons, p)>;
  eqs := SetToSequence({
    S.((&*[R.i : i in s[1..d]]) @ mon_index) *
    S.((&*[R.i : i in s[d+1..2*d]]) @ mon_index) -
    S.((&*[R.i : i in s[1..d-1]] * R.(s[d+1])) @ mon_index) *
    S.((&*[R.i : i in s[d+2..2*d]] * R.(s[d])) @ mon_index) :
  s in Subsequences({1..n},2*d)});
  return FreeHomogeneousPolys(eqs);
end function;

//Generating the equations of Veronese embeddings is expensive with my
//implementation. This saves the equations to a magma file.
//The dollar signs need to be replaced with the letter "R".
PrecomputeVeroneseEquation := procedure(F, n, d)
  eqs := VeroneseEquations(n, d);
  s := Sprintf("veronese_%o_%o := function()\n", n, d) cat
      "\tR := PolynomialRing(IntegerRing(), NumberOfMonomials(" cat 
      Sprintf("%o, %o));\n \treturn %m;\n", n, d, eqs) cat
      "end function;\n";
  PrintFile(F, s);
end procedure;

GetVeroneseEquations := function(n, d)
  return eval Sprintf("return veronese_%o_%o();", n, d);
end function;

//Checks if the projective varieties defined by sequences of equations
//are projectively equivalent under the projective transformation
//represented by T.
CheckProjectiveEquivalence := function(eqs_l, eqs_r, T)
  R := Parent(eqs_l[1]);
  I_l := ideal< R | [PolySubstitution(e, T) : e in eqs_l]>;
  I_r := ideal< R | eqs_r>;
  return I_l eq I_r;
end function;

CheckEquivalenceToVeronese := function(eqs, T, n, d)
  k := BaseRing(T);
  r := NumberOfMonomials(n, d);
  veqs := GetVeroneseEquations(n, d);
  ChangeUniverse(~veqs, PolynomialRing(k, r));
  return CheckProjectiveEquivalence(eqs, veqs, T);
end function;

RandomElements := function(L, n)
  s := #L-1;
  res := {};
  repeat
    Include(~res, Random(s) + 1);
  until #res eq n;
  return [L[i] : i in res];
end function;

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
