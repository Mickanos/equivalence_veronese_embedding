
// input: A semi-simple Lie algebra L
// output: An extension of the base field of L,
// the base change of L and a split Cartan subalgebra of this base change.
BaseChangeAndSplitCartan := function(L)
  H := CartanSubalgebra(L);
  B := [AdjointMatrix(L, b) : b in Basis(H)];
  facto := &cat[Factorisation(CharacteristicPolynomial(b)) : b in B];
  degree := Lcm([Degree(f[1]) : f in facto]);
  k := BaseField(L);
  K := ext<k | degree>;
  LK, base_change_map := ChangeRing(L, K);
  HK := sub<LK | [b @ base_change_map : b in Basis(H)]>;
  return K, LK, HK, base_change_map;
end function;

// Recovers the dimension of the Cartan subalgebra from the number of
// roots in the root system.
CartanDimFromRootNumber := function(n)
  b, r := IsSquare(1 + 4*n);
  assert b;
  return (r - 1) div 2;
end function;

// See Section 5.11 of De Graaf - Lie Algebras, Theory and Algorithms
// Relies on Magma's convention on the ordering of roots. 
// Might break upon future updates, although very unlikely.
CanonicalGenerators := function(root_vecs)
  s := CartanDimFromRootNumber(#root_vecs);
  t := #root_vecs div 2;
  xs := root_vecs[1..s];
  ys := [2*Colinearity((x*y)*x, x) * y where y is root_vecs[i+t] : i->x in xs];
  hs := [x * ys[i] : i->x in xs];
  return xs, ys, hs;
end function;

//Decompose the positive roots of the system as sums of simple roots.
DecomposeRoots := function(roots, simple_roots)
  splits := [[] : _ in [1..#roots div 2]];
  n := 1;
  while [] in splits do
    for s in CartesianPower([1..#simple_roots], n) do
      i := Index(roots, &+[simple_roots[i] : i in s]);
      if i gt 0 then
        splits[i] := [t : t in s]; 
      end if;
    end for;
    n +:= 1;
  end while;
  return splits;
end function;

// Input : A Lie Algebra L with a split Cartan subalgebra H.
// Output : An isomorphism to a normalised Lie Algebra, and said Lie Algebra.
NormaliseSplitLieAlgebra := function(L, H)
  roots, root_vectors, simple_roots := RootSystem(L, H);
  xs, ys, hs := CanonicalGenerators(root_vectors);
  splits := DecomposeRoots(roots, simple_roots);
  pos := [&*[xs[i] : i in s]: s in splits];
  neg := [&*[ys[i] : i in s]: s in splits];
  Basis := pos cat hs cat neg;
  return ChangeBasis(L, Basis);
end function;

//Produces Lie algebras gln and sln, with a projection and a lifting map.
gln_sln := function(k, n)
  Mat := MatrixAlgebra(k, n);
  A, phi := Algebra(Mat);
  gln, psi := LieAlgebra(A);
  mat_to_gln := phi * psi;
  sln, proj := quo<gln | Basis(Center(gln))>;
  lifts := [(M - (Trace(M)/n) * One(Mat)) @ mat_to_gln
    where M is S @@ (mat_to_gln * proj) : S in Basis(sln)];
  lift_map := hom< sln -> gln| lifts>;
  return gln, sln, mat_to_gln, lift_map;
end function;

//Given a Lie algebra isomorphic to some sl_n(k), computes an enveloping
//algebra following the algorithm from Section 2.2 of Pilnikova's thesis.
EnvelopingAlgebra := function(L)
  K, LK, HK, bc_map := BaseChangeAndSplitCartan(L);
  NL, Liso := NormaliseSplitLieAlgebra(LK, HK);
  _, n := IsSquare(Dimension(L) + 1);
  gln, sln, mat_to_gln, sln_to_gln := gln_sln(K, n);
  D := SplittingCartanSubalgebra(sln);
  NM, Miso := NormaliseSplitLieAlgebra(sln, D);
  iiso := hom < NL -> NM | Basis(NM)>;
  lie_iso := Liso * iiso * Inverse(Miso);
  assert IsIsomorphism(lie_iso);
  rho := bc_map * lie_iso * sln_to_gln;
  if K eq BaseRing(L) then
    A, phi := Algebra(Domain(mat_to_gln));
    return A, Inverse(phi) * mat_to_gln, rho;
  end if;
  k := BaseField(L);
  d := Degree(K,k);
  AssocBasis := [MatrixRestrictionOfScalars(k, b @ (rho * Inverse(mat_to_gln))):
    b in Basis(L)];
  Mdn := MatrixAlgebra(k, d*n);
  A, psi := Algebra(sub<Mdn | AssocBasis>);
  A_Lie, phi := LieAlgebra(A);
  env := hom< L -> A_Lie | [b @ (psi * phi) : b in AssocBasis]>;
  return A, phi, env;
end function;

//Outputs an isomorphism from the Lie algebra L to sln.
//Technically, the map just gives images as matrices, not as element of
//a Lie algebra. This is more convenient for our purposes.
SplitSln := function(L)
  A, phi, env := EnvelopingAlgebra(L);
  psi := SplitMatrixAlgebra(A);
  return env * Inverse(phi) * psi;
end function;