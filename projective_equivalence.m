// *******************************
// ** COMPUTING THE LIE ALGEBRA **
// *******************************

ComputeLieAlgebraBasis := function(eqs, r : f := 1, verbose := false)
  eqs := [QuadricToMatrix(e): e in eqs];
  F := BaseRing(eqs[1]);
  n := Nrows(eqs[1]);
  AMod, Quo := quo<KMatrixSpace(F, n, n) | eqs>;
  n_eqs := Ceiling(f * #eqs);
  count := 0;
  repeat
    A := RandomElements(eqs, n_eqs);
    M := HorizontalJoin([Matrix([Eltseq(Quo(Transpose(b)*a + a*b)) :
        b in Basis(MatrixAlgebra(F,n))]): a in A]);
    M := Transpose(M);
    RemoveZeroRows(~M);
    M := Transpose(M);
    count +:=1;
    if IsDivisibleBy(count, 5) then
        printf "Warning: already %o tries and the Lie algebra could not", count;
        print " be computed.";
    end if;
  until Rank(M) eq n^2 - r^2;
  B := Basis(Nullspace(M));
  printf "Lie algebra computed in %o tries.\n", count;
  res := [Matrix(F,n,n,Eltseq(b)): b in B];
    if verbose then
      print "We found a basis for the Lie algebra of the variety. Is is:";
      print res;
    end if;
  return res;
end function;

ComputeLieAlgebraBasisHomogeneous := function(pols)
  // algorithm for computing the Lie algebra of a scheme defined in terms
  // of homogeneous polynomials, all having the same degree
  // (this should also work for the quadratic case, but should be slower
  //  because it involves more polynomial arithmetic)
  deg := Degree(pols[1]);
  R := Parent(pols[1]);
  F := BaseRing(R);
  n := Rank(R);
  mons := MonomialsOfDegree(R, deg);
  N := #mons;
  V := VectorSpace(F, N);
  W := sub<V | [PolyToVector(f, mons) : f in pols] >;
  U, Quo := quo<V | W>;
  r := Dimension(U);
  basis := Basis(MatrixAlgebra(F, n));
  M := [];
  for b in basis do
    for f in pols do
      M cat:= Eltseq(Quo(PolyToVector(&+[&+[b[i][j]*R.j*Derivative(f, i) : j in [1..n]] : i in [1..n]], mons)));
    end for;
  end for;
  M := Matrix(n^2, #pols*r, M);
  B := Basis(Nullspace(M));
  res := [Matrix(F,n,n,Eltseq(b)): b in B];
  return res;
end function;

ComputeLieAlgebra := function(eqs, n, quotient: proj := 0)
  R := Parent(eqs[1]);
  k := BaseRing(R);
  N := Rank(R);
  gln := MatrixLieAlgebra(k, N);

  if IsZero(k!2) then
    basis := ComputeLieAlgebraBasisHomogeneous(eqs);
  else
    basis := ComputeLieAlgebraBasis(eqs, n);
  end if;

  if quotient then
    assert proj cmpne 0;
    target := Codomain(proj);
    basis := [b @ proj : b in basis];
    Exclude(~basis, Zero(target));
    g, rep := sub<target | basis>;
  else
    g, inj := sub<gln | basis>;
    g, conv := LieAlgebra(g);
    rep := Inverse(conv) * inj;
  end if;
  return g, rep;
end function;

//Takes two isomorphic Lie algebras embedded in gl_n.
//They should be represented as one list of triples of matrices
//corresponding to respective basis elements of each Lie algebras
//that are images of one another by a Lie algebra isomorphism.
//Elements two and three are conjugate by the outer automorphism of gl_n.
//Outputs an isomorphism of the natural representation. That is,
//an invertible matrix T in gl_n such that the second Lie algebra is the
//conjugate of the first by T.
LieAlgebraRepresentationIsomorphism := function(rep1, rep2)

end function;

LieAlgebraProjectiveRepresentationIsomorphism := function(rep1, rep2, lift_big)
  g1 := Domain(rep1);
  g2 := Domain(rep2);
  _, n := IsSquare(Dimension(g1)+1);
  k := BaseRing(g1);
  MA := Codomain(lift_big);
  _, proj_small, lift_small := PrepareGlnQuotient(k, n);
  gln := Domain(proj_small);
  graph := lift_small * GraphAuto(gln) * proj_small;
  half_iso1 := SplitGlnQuotient(g1, proj_small);
  half_iso2 := Inverse(SplitGlnQuotient(g2, proj_small));
  isoms := [half_iso1 * half_iso2, half_iso1 * graph * half_iso2];
  for iso in isoms do
    system := Matrix([
      &cat[
        Eltseq((a @ rep1 @ lift_big) * P - P * (a @ iso @ rep2 @ lift_big))
      : a in Basis(g1)]
    : P in Basis(MA)]);
    ker := Nullspace(system);
    if Dimension(ker) eq 1 then
      return MA!Eltseq(Basis(ker)[1]);
    end if;
  end for;
end function;

//Given quadric equations for a projective variety, computes a projective
//Equivalence to the Veronese embedding of degree d with n variables.
ComputeProjectiveEquivalence := function(eqs_1, eqs_2, n, d : f := 1, verbose := false)
  R := Parent(eqs_1[1]);
	k := BaseRing(R);
  special_case := IsZero(k!n) and IsZero(k!d);
  if special_case then
    N := Rank(R);
    _, proj_big, lift_big := PrepareGlnQuotient(k, N: normalise := true);
  else
    proj_big := 0;
  end if;
  g1, rep1 := ComputeLieAlgebra(eqs_1, n, special_case : proj := proj_big);
  g2, rep2 := ComputeLieAlgebra(eqs_2, n, special_case : proj := proj_big);
  if special_case then
    return LieAlgebraProjectiveRepresentationIsomorphism(rep1, rep2, lift_big);
  else
    return LieAlgebraRepresentationIsomorphism(rep1, rep2);
  end if;
end function;