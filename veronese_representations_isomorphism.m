/*****************************************************************
*              Veronese Representation Isomorphism               *
*****************************************************************/

/*
  Computing isomorphisms between Lie algebra representations isomorphic to
  representations induces by Veronese varieties.
*/

forward CompatibleIsomorphismsGln;
forward CompatibleIsomorphismsNotGln;
forward LieAlgebraRepresentationIsomorphism;

/*
  Compute an isomorphism between two representations, themselves isomorphic
  to the Lie algebra representation attached to the Veronese (n-1)-dimensional
  variety of degree d.
  Inputs:
    rep1, rep2: Lie algebra representations isomorphic to the Lie algebra
      of some Veronese variety.
    n: The dimension of the Veronese variety.
    d: The degree of the Veronese variety.
*/
VeroneseRepresentationsEquivalence := function(rep1, rep2, n, d)
	k := BaseRing(Domain(rep1));
  special_case := IsZero(k!(n + 1)) and IsZero(k!d);

  if special_case then
    isos := CompatibleIsomorphismsNotGln(rep1, rep2);
  else
    isos := CompatibleIsomorphismsGln(rep1, rep2);
  end if;

  return LieAlgebraRepresentationIsomorphism(rep1, rep2, isos);
end function;

/*
  Computes the list of eigenvalues of a matrix ordered by increasing
  multiplicities.
  Inputs:
    - M: A matrix.
*/
SortedEigenvalues := function(M)
  ev := SetToSequence(Eigenvalues(M));
  Sort(~ev, func<x, y | x[2] - y[2]>);
  return [e[1] : e in ev];
end function;

/*
  Compute a sequence of isomorphisms between the domains of rep1 and rep2, 
  themselves isomorphic to gl_n. It is assumed that rep1 and rep2 are isomorphic
  to the representation attached to a Veronese variety.
  It is guaranteed that one of the isomorphisms in the output underlies an
  isomorphism of representations.
  Inputs:
    - rep1, rep2: Representations of Lie algebras isomorphic to a representation
    attached to a Veronese variety, and with domains isomorphic to gl_n.
*/
CompatibleIsomorphismsGln := function(rep1, rep2)
  g1 := Domain(rep1);
  g2 := Domain(rep2);

  half_iso1 := IsomorphismToGln(g1);
  half_iso2 := Inverse(IsomorphismToGln(g2));
  gln := Domain(half_iso2);
  graph := GraphAutomorphismGln(gln);

  e := gln.1 @@ half_iso1;
  ev_target := SortedEigenvalues(e @ rep1);
  ev_start := SortedEigenvalues(e @ half_iso1 @ half_iso2 @ rep2);

  a := (ev_target[2] - ev_target[1]) / (ev_start[2] - ev_start[1]);
  step := (One(gln) @ half_iso2 @ rep2)[1,1];
  lambda := (a * ev_target[1] - ev_start[1]) / step;
  h := CenterAutomorphismGln(gln, lambda);

  if IsOdd(Characteristic(BaseRing(gln))) then
    if a eq -1 then
      h *:= graph;
    end if;
    return [half_iso1 * h * half_iso2];
  else
    return [half_iso1 * h * half_iso2, half_iso1 * graph * h * half_iso2];
  end if;
end function;

/*
  Compute a sequence of isomorphisms between the domains of rep1 and rep2, 
  themselves isomorphic to (gl_n / k I_n) \oplus k. It is assumed that rep1 and 
  rep2 are isomorphic to the representation attached to a Veronese variety.
  It is guaranteed that one of the isomorphisms in the output underlies an
  isomorphism of representations.
  Inputs:
    - rep1, rep2: Representations of Lie algebras isomorphic to a representation
      attached to a Veronese variety, and with domains isomorphic to
      (gl_n / k I_n) \oplus k.
*/
CompatibleIsomorphismsNotGln := function(rep1, rep2);
  g1 := Domain(rep1);
  g2 := Domain(rep2);
  k := BaseRing(g1);
  _, n := IsSquare(Dimension(g1));

  L, inj_ext, proj_ext, lift_gln, proj_gln := ConstructNotGln(k, n);
  d := Dimension(L);
  half_iso1 := IsomorphismToNotGln(g1, inj_ext, proj_gln);
  half_iso2 := Inverse(IsomorphismToNotGln(g2, inj_ext, proj_gln));

  c := BasisElement(L, 1);
  c1_coef := (c @@ half_iso1 @ rep1)[1, 1];
  c2_coef := (c @ half_iso2 @ rep2)[1, 1];
  e := BasisElement(L, 2) @@ half_iso1;
  ev_target := SortedEigenvalues(e @ rep1);
  ev_start := SortedEigenvalues(e @ half_iso1 @ half_iso2 @ rep2);
  a := (ev_target[2] - ev_target[1]) / (ev_start[2] - ev_start[1]);
  lambda := a*c1_coef / c2_coef;
  mu := (a * ev_target[1] - ev_start[1]) / c1_coef;

  graph := GraphAutomorphismNotGln(L, inj_ext, proj_ext, lift_gln, proj_gln);
  h := CenterAutomorphismNotGln(L, lambda);
  extra := ExtraAutomorphismNotGln(L, mu);

  if IsOdd(Characteristic(BaseRing(L))) then
    if a eq -1 then
      h *:= graph;
    end if;
    isos := [half_iso1 * h * extra * half_iso2];
  else
    isos := [half_iso1 * h * extra * half_iso2,
            half_iso1 * graph * h * extra * half_iso2];
  end if;

  return isos;
end function;

/*
  Computes an isomorphism between Lie algebras rep1 and rep2, assuming that
  isos is a sequence of isomorphisms between their domains, such that at least
  one of them underlies such a representation isomorphism.
  Inputs:
    - rep1, rep2: Representations of Lie algebras.
    - isos: A sequence of isomorphisms between the domains of rep1 and rep2.
*/
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