//Returns scalar t such that t*a eq b;
//Throws an error if a and b aren't colinear vectors.
Colinearity := function(a, b)
  i := Index([IsZero(c) : c in Eltseq(a)], false);
  t := b[i]/a[i];
  assert t*a eq b;
  return t;
end function;

//Outputs the elementary matrix of size mxn with 1 in position (i,j), and 0
//everywhere else.
ElementaryMatrix := function(k, m, n, i, j)
  M := ZeroMatrix(k, m, n);
  M[i,j] := 1;
  return M;
end function;

//Computes an isomorphism to an associative matrix algebra
SplitMatrixAlgebra := function(A)
  _, n := IsSquare(Dimension(A));
  k := BaseField(A);
  MA := MatrixAlgebra(k, n);
  I := MinimalRightIdeals(A : Limit := 1)[1];
  return map<A -> MA | a :-> Matrix([Coordinates(I, e*a): e in Basis(I)])>;
end function;

//p is a polynomial in n variables and M is a square matrix of order n.
//Computes the polynomial obtained from p by linear transformation of the
//variables.
PolySubstitution := function(p, M)
  R := Parent(p);
  n := Rank(R);
  return Evaluate(p, [&+[r[i]*R.i : i in [1..n]]: r in Rows(M)]);
end function;

//Computes the number of degree d homogeneous monomials with n indeterminates
NumberOfMonomials := function(n, d)
  return Binomial(n+d-1, d);
end function;

PolyToVector := function(P, mons)
	return Vector([MonomialCoefficient(P, m) : m in mons]);
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
  return [&+[v[i]*m : i->m in mons]: v in Basis(space)], space, mons;
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
  s := Sprintf("veronese_%o_%o := function()\n \treturn %m;\n", n, d, eqs) cat
      "end function;\n";
  PrintFile(F, s);
end procedure;

//Recover equations for the Veronese variety from the appropriate function.
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

//Outputs a random subsequence of L of size n
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
LieAlgebraVeroneseEmbeddingOld := function(k, n, d)
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

forward ComputeLieAlgebra;
forward ComputeLieAlgebraHomogeneous;
forward SplitGln;

LieAlgebraVeroneseEmbedding := function(k, n, d: f := 1)
	r := NumberOfMonomials(n, d);
	eqs := GetVeroneseEquations(n, d);
	ChangeUniverse(~eqs, PolynomialRing(k, r));
	if IsZero(k!2) then
		g, nat := ComputeLieAlgebraHomogeneous(eqs);
	else
		g, nat := ComputeLieAlgebra(eqs, n: f := f);
	end if;
	g_to_gln := SplitGln(g);
	return Inverse(g_to_gln) * nat;
end function;

//Input: A polynomial P over some field K, with subfield k.
//Output: A sequence of polynomials over k which combine into P with coefficients the basis of K over k.
Polyseq := function(P, k)
	d := Degree(BaseRing(Parent(P)), k);
	R := ChangeRing(Parent(P), k);
	if IsZero(P) then
		return [Zero(R) : _ in [1..d]];
	end if;
	coeffs, monomials := CoefficientsAndMonomials(P);
	coeffs_of_coeffs := [Eltseq(c, k): c in coeffs];
	polys_k := [R | ChangeRing(&+[c[i] * monomials[j]
		: j->c in coeffs_of_coeffs], k): i in [1..d]];
	return polys_k;
end function;

//Descends A to an associative algebra over k.
//Assumes that the structure constants of A all lie in k,
//even if A is defined over an extension.
DescendAssociativeAlgebra := function(A, k)
	d := Dimension(A);
	Q := [[ChangeUniverse(Eltseq(BasisProduct(A, i, j)), k): j in [1..d]]: i in [1..d]];
	return AssociativeAlgebra<k, d | Q : Check := false>;
end function;

//Returns the list of values taken by an associative array. Now implemented in Magma, left for retro-compatibility.
AppearsIn := function(A, v)
	return &or[A[k] eq v : k in Keys(A)];
end function;

GraphAuto := function(gln)
	return map<gln -> gln | a :-> gln!(Transpose(-Matrix(a)))>;
end function;

GraphAutoSpecialCase := function(e, inj_ext, proj_ext, lift_gln, proj_gln)
  return map<e -> e | a :-> (-Transpose(a @ proj_ext @ lift_gln)) @ proj_gln @ inj_ext - (a - a @ proj_ext @ inj_ext)>;
end function;

h_isom := function(gln, lambda)
  assert lambda * Degree(gln) ne -1;
	return map<gln -> gln | a :-> a + lambda * Trace(a) * One(gln)>;
end function;

h_isom_special_case := function(e, lambda)
  assert not IsZero(lambda);
  d := Dimension(e);
  return hom<e -> e | [lambda * BasisElement(e, 1)] cat Basis(e)[2..d]>;
end function;

extra_isom_special_case := function(e, lambda)
  d := Dimension(e);
  x := BasisElement(e, 2);
  c := BasisElement(e, 1);
  return hom<e -> e | [c, x + lambda * c] cat Basis(e)[3..d]>;
end function;

PrepareGlnQuotient := function(k, n)
  gln := MatrixLieAlgebra(k, n);
  Mn := MatrixAlgebra(k, n);
  In := IdentityMatrix(k, n);
  gln_struc, conv := LieAlgebra(gln);
  g, proj, partial_lift := QuotientWithPullback(gln_struc, Center(gln_struc));
  proj := conv * proj;
    lift := map<g -> Mn | a :-> Matrix(b @@ conv) where b, _ is a @ partial_lift>;
  return g, proj, lift;
end function;

forward trivial_central_extension;
PrepareGlnModInPlusk := function(k, n)
  g, proj_gln, lift_gln := PrepareGlnQuotient(k, n);
  e, inj_ext, proj_ext := trivial_central_extension(g);
  s := sub<e | [a*b : a, b in Basis(e)]>;
  gln := Domain(proj_gln);
  x := gln.1 @ proj_gln @ inj_ext;
  c := BasisElement(Center(e), 1);
  new_basis := [c, x] cat Basis(s);
  e, conv := ChangeBasis(e, new_basis);
  return e, inj_ext * conv, Inverse(conv) * proj_ext, lift_gln, proj_gln;
end function;

SortedEigenvalues := function(M)
  ev := SetToSequence(Eigenvalues(M));
  Sort(~ev, func<x, y | x[2] - y[2]>);
  return [e[1] : e in ev];
end function;

LieAlgebraFromMatrixGen:= function(gen)
  ML := Universe(gen);
  s, inj := sub<ML | gen>;
  g, conv := LieAlgebra(s);
  rep := Inverse(conv) * inj;
  return g, rep;
end function;