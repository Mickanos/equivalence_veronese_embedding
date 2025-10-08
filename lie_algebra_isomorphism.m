//Compute the roots and corresponding spaces of the adjoint representation of split Cartan subalgebra H on L.
ComputeRoots := function(L, H)
	mats := [Matrix(-AdjointMatrix(L, h)) : h in Basis(H)];
	spaces, roots := CommonEigenspaces(mats);
	roots := [Vector(r) : r in roots];
	i := Index(roots, Parent(roots[1])!0);
	Remove(~spaces, i);
	Remove(~roots, i);
	return spaces, roots;
end function;

Char2SpaceBreak := function(L, spaces, roots, i)
	F := BaseRing(L);
	R := PolynomialRing(F);
	root := roots[i];
	space := spaces[i];
	j := Index([j ne i and (r + root) in roots : j -> r in roots], true);
	k := Index(roots, root + roots[j]);
	pivot_space := spaces[j];
	target_space := spaces[k];
	ba := Basis(space);
	mats := [Matrix([Coordinates(target_space, Vector(a*L!v)) : v in Basis(pivot_space)]): a in ba];
	a := mats[1];
	b := mats[2];

	//Equation for the cancellation of the determinant of a combination of the two matrices
	mid := a[1,1]*b[2,2] + a[2,2]*b[1,1] - a[1,2]*b[2,1] - a[2,1]*b[1,2];
	da := Determinant(a);
	db := Determinant(b);
	if IsZero(da) then
		return [L!ba[1], IsZero(db) select L!ba[2] else L!(ba[1]) - mid/db * ba[2]];
	end if;
	zeros := [t[1] : t in Roots(R![da, mid, db])];
	return [L!(ba[1] + x*ba[2]) : x in zeros];
end function;


Eigenbasis := function(L, spaces, roots)
	return [
		Dimension(space) eq 1 select [L!b : b in Basis(space)] else
		Char2SpaceBreak(L, spaces, roots, i)
		: i -> space in spaces];
end function;

IndexRoots := function(roots)
	n := Degree(roots[1]);
	res := AssociativeArray();
	res[<1,2>] := roots[1];
	res[<2,1>] := -roots[1];
	//The loop invariant is that at the start of iteration i, all the roots of the 
	//form Phi_{kl} such that k < l <= i are properly indexed in res.
	for i in [2..n-1] do
		res[<i,i+1>] := [r : r in roots | res[<1,i>] + r in roots and not AppearsIn(res, r)][1];
		res[<1,i+1>] := res[<1,i>] + res[<i,i+1>];
		res[<i+1,i>] := -res[<i,i+1>];
		res[<i+1,1>] := -res[<1,i+1>];
		for j in [2..i-1] do
			res[<j,i+1>] := res[<1, i+1>] - res[<1,j>];
			res[<i+1,j>] := -res[<j,i+1>];
		end for;
	end for;
	return res;
end function;

GetNormalisedBasis := function(roots, indexed_roots, eigenbasis, H)
	n := Degree(roots[1]);
	p := Characteristic(BaseRing(roots[1]));
	L := Parent(eigenbasis[1][1]);
	res := AssociativeArray(); 
	k := BaseRing(H);
	if p gt 2 then
		for key in Keys(indexed_roots) do
			i := Index(roots, indexed_roots[key]);
			res[key] := eigenbasis[i][1];
		end for;
	else
		ell := Index(roots, indexed_roots[<1,2>]);
		res[<1,2>] := eigenbasis[ell][1];
		res[<2,1>] := eigenbasis[ell][2];
		for i in [2..n-1] do
			for j in [2..i] do
				ell := Index(roots, indexed_roots[<j,i+1>]);
				res[<j,i+1>] := [e : e in eigenbasis[ell] | not IsZero(res[<1,j>] * e)][1];
				res[<i+1,j>] := [e : e in eigenbasis[ell] | e ne res[<j,i+1>]][1];
			end for;
			ell := Index(roots, indexed_roots[<1,i+1>]);
			res[<i+1,1>] := [e : e in eigenbasis[ell] | not IsZero(res[<2,i+1>] * e)][1];
			res[<1,i+1>] := [e : e in eigenbasis[ell] | e ne res[<i+1,1>]][1];
		end for;
	end if;

	//Now, to find e_1_1.

	total_space := Module(L);
	bad_space := sub<total_space | [Vector(res[<i,i+1>] * res[<i+1, i>]): i in [1..n-1]]>;
	system := Transpose(Matrix([indexed_roots[<i,i+1>]: i in [1..n-1]]));
	sol, nullspace := Solution(system, Vector([One(k)] cat [Zero(k) : _ in [1..n-2]]));
	sol := L!(H!Eltseq(sol));
	if not total_space!sol in bad_space then
		res[<1,1>] := sol;
	else
		bas_nul := [L!(H!Eltseq(b)) : b in Basis(nullspace)];
		exit_ticket := [b : b in bas_nul |
			not total_space!b in bad_space][1];
		res[<1,1>] := sol + exit_ticket;
	end if;

	//And the rest of H.
	for k in [2..n] do
		mat_1 := Transpose(Matrix([Eltseq(indexed_roots[<k,1>])]
					cat [Eltseq(indexed_roots[<i,j>])
						: i, j in [1..n] | i ne j and i ne k and j ne k]));
		quotient, proj := quo<total_space | [Vector(res[<1,k>] * res[<k,1>])]>;
		mat_2 := Matrix([Eltseq((total_space!(L!h)) @ proj) : h in Basis(H)]);
		N := (n-1)*(n-2);
		target := Vector([1] cat [0 : _ in [1..N]] cat Eltseq((total_space!res[<1,1>]) @ proj));
		sol := Solution(HorizontalJoin(mat_1, mat_2), target);
		res[<k, k>] := L!H!(Eltseq(sol));
	end for;

	//Some rescaling is needed.
	for i in [2..n-1], j in [i+1..n] do
		lambda := Colinearity(res[<1,i>]*res[<i,j>],res[<1,j>]);
		res[<i,j>] *:= lambda;
	end for;
	for i in [2..n], j in [1..i-1] do
		lambda := Colinearity(res[<i,j>]*res[<j,i>],res[<i,i>] - res[<j,j>]);
		res[<i,j>] *:= lambda;
	end for;

	return [res[<i,j>]: i,j in [1..n]];
end function;

NormaliseSplitLieAlgebra := function(L, H)
	spaces, roots := ComputeRoots(L, H);
	eigenbasis := Eigenbasis(L, spaces, roots);
	indexed_roots := IndexRoots(roots);
	basis := GetNormalisedBasis(roots, indexed_roots, eigenbasis, H);
	return ChangeBasis(L, basis);
end function;

// input: A Lie algebra L
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

AdjustStructureConstants := function(L, iso)
	MA := Codomain(iso);
	K := BaseRing(MA);
	k := BaseRing(L);
	d := Degree(K, k);
	R := PolynomialRing(K, d);
	Rk := PolynomialRing(k, d);
	SeqSet := Parent([Rk.1]);
	lambda := &+[b * R.i : i-> b in Basis(K, k)];
	matrices := [ChangeRing(b @ iso, R) : b in Basis(L)];
	char_polys := [CharacteristicPolynomial(M): M in matrices];
	t := Parent(char_polys[1]).1;
	evals := [Evaluate(P, t - lambda * Trace(matrices[i])): i -> P in char_polys];
	coefficients := &cat[Coefficients(e): e in evals];
	polys_k := &cat[SeqSet | Polyseq(P, k)[2..d] : P in coefficients];
	I := ideal<Rk | polys_k>;
	points := [K!TupleToSequence(x): x in Variety(I)];
	lambda := [p : p in points | Degree(MA)*p ne -1][1];
	adjustment := map<MA -> MA | M :-> M + lambda * Trace(M) * One(MA)>;
	return iso * adjustment;
end function;
	
//Given a Lie algebra isomorphic to some gl_n(k), computes an enveloping
//algebra following the algorithm from Section 2.2 of Pilnikova's thesis.
//Outputs either true and an isomorphism to M_n(k), or false and an injection of L into M_n(K)
//such that the image of L is stable by multiplication.
EnvelopingAlgebra := function(L)
  K, LK, HK, bc_map := BaseChangeAndSplitCartan(L);
  NL, Liso := NormaliseSplitLieAlgebra(LK, HK);
  _, n := IsSquare(Dimension(L));
  iso := bc_map * Liso;
  Ma := MatrixAlgebra(K, n);
  if K eq BaseRing(L) then
  	M := Matrix([Eltseq(b @ iso): b in Basis(L)]);
	iM := M^-1;
	iso := map< L -> Ma | x :-> Ma!Eltseq(Vector(x) * M), y :-> L!Eltseq(Vector(y) * iM)>;
  	return true, iso;
  end if;
  iso := map<L -> Ma | b :-> Ma!Eltseq(b @ iso)>;
  iso := AdjustStructureConstants(L, iso);
  MaAss, phi := Algebra(Ma);
  A := sub<MaAss | [b @ iso @ phi: b in Basis(L)]>;
  A, psi := ChangeBasis(A, [b @ iso @ phi: b in Basis(L)]);
  B := DescendAssociativeAlgebra(A, BaseRing(L));
  final_iso := hom<L -> B | Basis(B)>;
  return false, final_iso;
end function;

//Outputs an isomorphism from the Lie algebra L to sln.
//Technically, the map just gives images as matrices, not as element of
//a Lie algebra. This is more convenient for our purposes.
SplitGln := function(L)
	done, phi := EnvelopingAlgebra(L);
	if done then
		return phi;
	end if;
	A := Codomain(phi);
	psi := SplitMatrixAlgebra(A);
	M := Matrix([Vector(b @ phi @ psi): b in Basis(L)]);
	iM := M^-1;
	MA := Codomain(psi);
	return map<L -> Codomain(psi) | x :-> MA!Eltseq(Vector(x) * M), y :-> L!Eltseq(Vector(y) * iM)>;
end function;
