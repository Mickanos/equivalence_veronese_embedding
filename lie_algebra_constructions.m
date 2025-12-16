GraphAutomorphismGln := function(gln)
	return map<gln -> gln | a :-> gln!(Transpose(-Matrix(a)))>;
end function;

GraphAutomorphismNotGln := function(e, inj_ext, proj_ext, lift_gln, proj_gln)
  return map<e -> e | a :-> (-Transpose(a @ proj_ext @ lift_gln)) @ proj_gln @ inj_ext - (a - a @ proj_ext @ inj_ext)>;
end function;

CenterAutomorphismGln := function(gln, lambda)
  assert lambda * Degree(gln) ne -1;
	return map<gln -> gln | a :-> a + lambda * Trace(a) * One(gln)>;
end function;

CenterAutomorphismNotGln := function(e, lambda)
  assert not IsZero(lambda);
  d := Dimension(e);
  return hom<e -> e | [lambda * BasisElement(e, 1)] cat Basis(e)[2..d]>;
end function;

ExtraAutomorphismNotGln := function(e, lambda)
  d := Dimension(e);
  x := BasisElement(e, 2);
  c := BasisElement(e, 1);
  return hom<e -> e | [c, x + lambda * c] cat Basis(e)[3..d]>;
end function;

ConstructGlnQuotient := function(k, n)
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
ConstructNotGln := function(k, n)
  g, proj_gln, lift_gln := ConstructGlnQuotient(k, n);
  e, inj_ext, proj_ext := trivial_central_extension(g);
  s := sub<e | [a*b : a, b in Basis(e)]>;
  gln := Domain(proj_gln);
  x := gln.1 @ proj_gln @ inj_ext;
  c := BasisElement(Center(e), 1);
  new_basis := [c, x] cat Basis(s);
  e, conv := ChangeBasis(e, new_basis);
  return e, inj_ext * conv, Inverse(conv) * proj_ext, lift_gln, proj_gln;
end function;

//Computes the Lie algebra of the Veronese variety of dimension n-1 and degree
//d.
VeroneseRepresentation := function(k, n, d)
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
    glN := MatrixLieAlgebra(k, #mons);
    derivative_map := map< gln -> glN
      | M :-> &+[M[i,j] * Mats[i][j]: i,j in [1..n]]>;
    if not IsZero(k!d) then
      return derivative_map;
    end if;
    if not IsZero(k!n) then
      I := (1 / n) * One(gln);
      return map< gln -> glN
        | M :-> (M - Trace(M) * I) @ derivative_map + Trace(M) * One(glN)>;
    end if;
    e, _, proj_ext, inj_gln := ConstructNotGln(k, n);
    return map <e -> glN | a :-> (a @ proj_ext @ inj_gln @ derivative_map) + a[1] * One(glN)>;
end function;