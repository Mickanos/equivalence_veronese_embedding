/*****************************************************************
*                      Lie Algebra Constructions                 *
*****************************************************************/

/*
  Functions computing various useful Lie algebras, automorphisms
  and representations.
*/

forward ConstructGlnQuotient;

/*
  Constructs the Lie algebra (gl_n(k) / k I_n) \oplus k. Is is isomorphic to
  gl_n unless n is zero in k.
  The basis of the output algebra is arranged so that its first element
  generated the center and its third to last elements yield the basis of its
  derived subalgebra.
  Inputs:
    - k: The base field.
    - n: The degree of the matrix algebra.
  Outputs:
    - e: The Lie algebra constructed, defined by structure constants.
    - inj_ext: The map from (gl_n / k I_n) into e.
    - proj_ext: The orthogonal projection from e into (gl_n / k I_n).
    - lift_gln: Some lifting map from (gl_n / k I_n) to gl_n.
    - proj_gln: The projection from gl_n to (gl_n / k I_n).
*/
ConstructNotGln := function(k, n)
  g, proj_gln, lift_gln := ConstructGlnQuotient(k, n);
  e, inj_ext, proj_ext := TrivialCentralExtension(g);
  s := sub<e | [a*b : a, b in Basis(e)]>;
  gln := Domain(proj_gln);
  x := gln.1 @ proj_gln @ inj_ext;
  c := BasisElement(Center(e), 1);
  new_basis := [c, x] cat Basis(s);
  e, conv := ChangeBasis(e, new_basis);
  return e, inj_ext * conv, Inverse(conv) * proj_ext, lift_gln, proj_gln;
end function;

/*
  Computes the Lie algebra representation attached to the Veronese variety of
  dimension n and degree d.
  Inputs:
    - k : The base field.
    - n : The dimension of the Veronese variety.
    - d : The degree of the Veronese variety.
*/
VeroneseRepresentation := function(k, n, d)
    n := n + 1;
    R := PolynomialRing(k, n);
    mons := SetToSequence(MonomialsOfDegree(R, d));
    op := [[map<R -> R | p :-> R.j * Derivative(p,i)>: j in [1..n]]:
        i in [1..n]];
    Mats := [[Matrix(
        k,
        [[MonomialCoefficient(im, col) : col in mons]
            where im is mon @ op[i][j]: mon in mons]
        ): j in [1..n]]: i in [1..n]];
    gln := MatrixLieAlgebra(k, n);
    gln_struc, conv := LieAlgebra(gln);
    glN := MatrixLieAlgebra(k, #mons);
    derivative_map := map< gln -> glN
      | M :-> &+[M[i,j] * Mats[i][j]: i,j in [1..n]]>;
    if not IsZero(k!d) then
      return Inverse(conv) * derivative_map;
    end if;
    if not IsZero(k!n) then
      I := (1 / n) * One(gln);
      corrected_map := map< gln -> glN
        | M :-> (M - Trace(M) * I) @ derivative_map + Trace(M) * One(glN)>;
      return Inverse(conv) * corrected_map;
    end if;
    e, _, proj_ext, inj_gln := ConstructNotGln(k, n);
    return map <e -> glN |
      a :-> (a @ proj_ext @ inj_gln @ derivative_map) + a[1] * One(glN)>;
end function;

/*
  Computes the so-called "graph automorphism" of the Lie algebra gl_n.
  That is, the map $M |--> -M^t.
  Inputs:
    - gln : The matrix Lie algebra gln.
*/
GraphAutomorphismGln := function(gln)
	return map<gln -> gln | a :-> gln!(Transpose(-Matrix(a)))>;
end function;

/*
  Outputs the automorphism of (gl_n / k I_n) \oplus k induced by the graph
  automorphism projected to (gl_n / k I_n).
  Inputs:
    Exactly the outputs of ConstructNotGln.
*/
GraphAutomorphismNotGln := function(e, inj_ext, proj_ext, lift_gln, proj_gln)
  return map<e -> e |
    a :-> (-Transpose(a @ proj_ext @ lift_gln)) @ proj_gln @ inj_ext -
      (a - a @ proj_ext @ inj_ext)>;
end function;

/*
  Outputs the automorphism of gl_n sending M to M + lambda * Tr(M) * I_n.
  Inputs:
    - gln : The matrix Lie algebra.
    - lambda : A base field element not equal to -1.
*/
CenterAutomorphismGln := function(gln, lambda)
  assert lambda * Degree(gln) ne -1;
	return map<gln -> gln | a :-> a + lambda * Trace(a) * One(gln)>;
end function;

/*
  Ouputs the automorphism of (gl_n / k I_n) \oplus k induced by the 
  multiplication-by-lambda automorphism of k.
  Inputs:
    - e : The Lie algebra (gl_n / k I_n) \oplus k.
    - lambda : A nonzero field element.
*/
CenterAutomorphismNotGln := function(e, lambda)
  assert not IsZero(lambda);
  d := Dimension(e);
  return hom<e -> e | [lambda * BasisElement(e, 1)] cat Basis(e)[2..d]>;
end function;

/*
  Outputs the automorphism of (gl_n / k I_n) \oplus k defined by a linear map
  from (gl_n / k I_n) to k with kernel its derived subalgebra.
  Inputs:
    - e : The Lie algebra (gl_n / k I_n) \oplus k.
    - lambda : A field element.
*/
ExtraAutomorphismNotGln := function(e, lambda)
  d := Dimension(e);
  x := BasisElement(e, 2);
  c := BasisElement(e, 1);
  return hom<e -> e | [c, x + lambda * c] cat Basis(e)[3..d]>;
end function;

/*
  Constructs the Lie algebra (gl_n / k I_n).
  Inputs:
    - k : The base field.
    - n : The order of the matrix algebra.
  Outputs:
    - g : The Lie algebra (gl_n / k I_n).
    - proj : The projection map from gl_n to g.
    - lift : Some linear lifting from g to gl_n.
*/
ConstructGlnQuotient := function(k, n)
  gln := MatrixLieAlgebra(k, n);
  Mn := MatrixAlgebra(k, n);
  In := IdentityMatrix(k, n);
  gln_struc, conv := LieAlgebra(gln);
  g, proj, partial_lift := QuotientWithPullback(gln_struc, Center(gln_struc));
  proj := conv * proj;
    lift := map<g -> Mn |
      a :-> Matrix(b @@ conv) where b, _ is a @ partial_lift>;
  return g, proj, lift;
end function;