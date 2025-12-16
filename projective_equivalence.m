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

ComputeLieAlgebra := function(eqs, n)
  R := Parent(eqs[1]);
  k := BaseRing(R);
  N := Rank(R);
  gln := MatrixLieAlgebra(k, N);

  if IsZero(k!2) then
    basis := ComputeLieAlgebraBasisHomogeneous(eqs);
  else
    basis := ComputeLieAlgebraBasis(eqs, n);
  end if;

  ChangeUniverse(~basis, gln);

  return LieAlgebraFromMatrixGen(basis);
end function;

CompatibleIsomorphismsGln := function(rep1, rep2)
  g1 := Domain(rep1);
  g2 := Domain(rep2);

  half_iso1 := SplitGln(g1);
  half_iso2 := Inverse(SplitGln(g2));
  gln := Domain(half_iso2);
  graph := GraphAuto(gln);

  e := gln.1 @@ half_iso1;
  ev_target := SortedEigenvalues(e @ rep1);
  ev_start := SortedEigenvalues(e @ half_iso1 @ half_iso2 @ rep2);

  a := (ev_target[2] - ev_target[1]) / (ev_start[2] - ev_start[1]);
  step := (One(gln) @ half_iso2 @ rep2)[1,1];
  lambda := (a * ev_target[1] - ev_start[1]) / step;
  h := h_isom(gln, lambda);

  if IsOdd(Characteristic(BaseRing(gln))) then
    if a eq -1 then
      h *:= graph;
    end if;
    return [half_iso1 * h * half_iso2];
  else
    return [half_iso1 * h * half_iso2, half_iso1 * graph * h * half_iso2];
  end if;
end function;

CompatibleIsomorphismsGlnModInPlusk := function(rep1, rep2);
  g1 := Domain(rep1);
  g2 := Domain(rep2);
  k := BaseRing(g1);
  _, n := IsSquare(Dimension(g1));

  L, inj_ext, proj_ext, lift_gln, proj_gln := PrepareGlnModInPlusk(k, n);
  d := Dimension(L);
  half_iso1 := SplitGlnQuotientTriviallyExtended(g1, inj_ext, proj_gln);
  half_iso2 := Inverse(SplitGlnQuotientTriviallyExtended(g2,
                                                        inj_ext,
                                                        proj_gln));
  graph := GraphAutoSpecialCase(L, inj_ext, proj_ext, lift_gln, proj_gln);
  c := BasisElement(L, 1);
  c1_coef := (c @@ half_iso1 @ rep1)[1, 1];
  c2_coef := (c @ half_iso2 @ rep2)[1, 1];
  h := h_isom_special_case(L, c1_coef / c2_coef);
  h_graph := graph * h_isom_special_case(L, -c1_coef / c2_coef);

  e := BasisElement(L, 2) @@ half_iso1;
  ev_target := SortedEigenvalues(e @ rep1);
  ev_start := SortedEigenvalues(e @ half_iso1 @ half_iso2 @ rep2);

  a := (ev_target[2] - ev_target[1]) / (ev_start[2] - ev_start[1]);
  lambda := (a * ev_target[1] - ev_start[1]) / c1_coef;
  extra := extra_isom_special_case(L, lambda);

  if IsOdd(Characteristic(BaseRing(L))) then
    if a eq -1 then
      h := h_graph;
    end if;
    isos := [half_iso1 * h * extra * half_iso2];
  else
    isos := [half_iso1 * h * extra * half_iso2, half_iso1 * graph * h * extra * half_iso2];
  end if;
  for iso in isos do
    print (c @@ half_iso1 @ rep1)[1,1];
    print (c @@ half_iso1 @ iso @ rep2)[1,1];
    print SortedEigenvalues(e @ rep1);
    print SortedEigenvalues(e @ iso @ rep2);
    print "****";
  end for;
  return isos;
end function;

LieAlgebraRepresentationIsomorphism := function(rep1, rep2, isos)
  g1 := Domain(rep1);
  N := Degree(Codomain(rep1));
  k := BaseRing(g1);
  MA := MatrixAlgebra(k, N);

  for iso in isos do
    system := Matrix([
      &cat[
        Eltseq(Matrix(a @ rep1) * P - P * Matrix(a @ iso @ rep2))
      : a in Basis(g1)]
    : P in Basis(MA)]);
    ker := Nullspace(system);
    if Dimension(ker) eq 1 then
      return MA!Eltseq(Basis(ker)[1]);
    end if;
  end for;
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
  /*
  if special_case then
    N := Rank(R);
    _, proj_big, lift_big := PrepareGlnQuotient(k, N: normalise := true);
  else
    proj_big := 0;
  end if;
  g1, rep1 := ComputeLieAlgebra(eqs_1, n, special_case : proj := proj_big);
  g2, rep2 := ComputeLieAlgebra(eqs_2, n, special_case : proj := proj_big);
  */
  g1, rep1 := ComputeLieAlgebra(eqs_1, n);
  g2, rep2 := ComputeLieAlgebra(eqs_2, n);

  if special_case then
    isos := CompatibleIsomorphismsGlnModInPlusk(rep1, rep2);
  else
    isos := CompatibleIsomorphismsGln(rep1, rep2);
  end if;

  return LieAlgebraRepresentationIsomorphism(rep1, rep2, isos);
/*
  if special_case then
    return LieAlgebraProjectiveRepresentationIsomorphism(rep1, rep2, lift_big);
  else
    return LieAlgebraRepresentationIsomorphism(rep1, rep2);
  end if;
*/
end function;