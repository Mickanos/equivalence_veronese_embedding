//Compute the roots and corresponding spaces of the adjoint representation of split Cartan subalgebra H on L.
ComputeRoots := function(L, H)
	mats := [Matrix(AdjointMatrix(L, h)) : h in Basis(H)];
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

GetIndexedRoot := function(ordered_roots, i, j)
	return [r[3] : r in ordered_roots | r[1] eq i and r[2] eq j][1];
end function;

FindIndexedRoot := function(roots, indexed_roots, i, j)
	return Index(roots, GetIndexedRoot(indexed_roots, i, j));
end function;

//This implementation is not terribly efficient but that part should be very fast anyway.
IndexRoots := function(roots)
	n := Degree(roots[1]);
	res := [<1, 2, roots[1]>];
	Append(~res, <2, 1, -roots[1]>);
	//The loop invariant is that at the start of iteration i, all the roots of the 
	//form Phi_{kl} such that k < l <= i are properly indexed in res.
	for i in [2..n-1] do
		phi_1_i := GetIndexedRoot(res, 1, i);
		phi_i_ip1 := [r : r in roots | phi_1_i + r in roots][1];
		phi_1_ip1 := phi_1_i + phi_i_ip1;
		Append(~res, <i, i+1, phi_i_ip1>);
		Append(~res, <i+1, i, -phi_i_ip1>);
		Append(~res, <1, i+1, phi_1_ip1>);
		Append(~res, <i+1, 1, -phi_1_ip1>);
		for j in [2..i-1] do
			phi_1_j := GetIndexedRoot(res, 1, j);
			phi_j_ip1 := [r : r in roots | r + phi_1_j eq phi_1_ip1][1];
			Append(~res, <j, i+1, phi_j_ip1>);
			Append(~res, <i+1, j, -phi_j_ip1>);
		end for;
	end for;
	return res;
end function;

GetNormalisedBasis := function(roots, indexed_roots, eigenbasis, H)
	n := Degree(roots[1]);
	p := Characteristic(BaseRing(roots[1]));
	L := Parent(eigenbasis[1][1]);
	res := [];
	k := BaseRing(H);
	if p gt 2 then
		for t in indexed_roots do
			i := Index(roots, t[3]);
			Append(~res, <t[1], t[2], eigenbasis[i][1]>);
		end for;
	else
		ell := FindIndexedRoot(roots, indexed_roots, 1, 2);
		Append(~res, <1, 2, eigenbasis[ell][1]>);
		Append(~res, <2, 1, eigenbasis[ell][2]>);
		for i in [2..n-1] do
			for j in [2..i] do
				ell := FindIndexedRoot(roots, indexed_roots, j, i+1);
				e_1_j := GetIndexedRoot(res, 1, j);
				e_j_ip1 := [e : e in eigenbasis[ell] | not IsZero(e_1_j * e)][1];
				e_ip1_j := [e : e in eigenbasis[ell] | e ne e_j_ip1][1];
				Append(~res, <j, i+1, e_j_ip1>);
				Append(~res, <i+1, j, e_ip1_j>);
			end for;
			ell := FindIndexedRoot(roots, indexed_roots, 1, i+1);
			e_2_ip1 := GetIndexedRoot(res, 2, i+1);
			e_ip1_1 := [e : e in eigenbasis[ell] | not IsZero(e_2_ip1 * e)][1];
			e_1_ip1 := [e : e in eigenbasis[ell] | e ne e_ip1_1][1];
			Append(~res, <1, i+1, e_1_ip1>);
			Append(~res, <i+1, 1, e_ip1_1>);
		end for;
	end if;

	//Now, to find e_1_1.
	system := Transpose(Matrix([Eltseq(GetIndexedRoot(indexed_roots, 1, 2))]
			cat [Eltseq(GetIndexedRoot(indexed_roots, i, i+1)): i in [2..n-1]]));
	sol, nullspace := Solution(system, Vector([One(k)] cat [Zero(k) : _ in [1..n-2]]));
	total_space := Module(Parent(res[1][3]));
	bad_space := sub<total_space | [Vector(GetIndexedRoot(res, i, i+1)
					* GetIndexedRoot(res, i+1, i)): i in [1..n-1]]>;
	sol := L!(H!Eltseq(sol));
	if not total_space!sol in bad_space then
		e_1_1 := sol;
		Append(~res, <1, 1, sol>);
	else
		bas_nul := [L!(H!Eltseq(b)) : b in Basis(nullspace)];
		exit_ticket := [b : b in bas_nul |
			not total_space!b in bad_space][1];
		e_1_1 := sol + exit_ticket;
	end if;
	Append(~res, <1, 1, e_1_1>);

	//And the rest of H.
	for k in [2..n] do
		mat_1 := Transpose(Matrix([Eltseq(GetIndexedRoot(indexed_roots, k, 1))]
					cat [Eltseq(GetIndexedRoot(indexed_roots, i, j))
						: i, j in [1..n] | i ne j and i ne k and j ne k]));
		quotient, proj := quo<total_space | [Vector(GetIndexedRoot(res, 1, k)
							* GetIndexedRoot(res, k, 1))]>;
		mat_2 := Matrix([Eltseq((total_space!(L!h)) @ proj) : h in Basis(H)]);
		N := (n-1)*(n-2);
		target := Vector([1] cat [0 : _ in [1..N]] cat Eltseq((total_space!e_1_1) @ proj));
		sol := Solution(HorizontalJoin(mat_1, mat_2), target);
		e_k_k := H!(Eltseq(sol));
		Append(~res, <k, k, e_k_k>);
	end for;
	return [GetIndexedRoot(res, i, j): i,j in [1..n]];
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
	k := BaseField(L);
	NL := Codomain(iso);
	K := BaseRing(NL);
	d := Degree(K, k);
	_, n := IsSquare(Dimension(L));
	MP := PolynomialRing(k, d);
	R := FieldOfFractions(MP);
	RL, rest := MyRestrictionOfScalars(NL, k);
	RLpol, base_change := ChangeRing(RL, R);
	I := NL!(Eltseq(IdentityMatrix(K, n)));
	Is := [R.i * ((t*I) @ rest @ base_change) : i -> t in Basis(K, k)];
	RLpol_changed := ChangeBasis(RLpol, [b + &+Is : b in Basis(RLpol)]);
	eqs := &cat[Eltseq(BasisProduct(RLpol_changed, i, j))[[ell : ell in [1..Dimension(RL)] | ell mod d ne 1]]
    		: i, j in [1..Dimension(RL)] | i mod d eq 1 and j mod d eq 1];
	I := ideal<MP | [Numerator(e) : e in eqs]>;
	assert IsZeroDimensional(I);
	lambda := K!(Variety(I)[1]);
	return ChangeBasis(NL, [b + lambda * I : b in Basis(NL)]);
end function;
	
//Given a Lie algebra isomorphic to some gl_n(k), computes an enveloping
//algebra following the algorithm from Section 2.2 of Pilnikova's thesis.
//Outputs either true and an isomorphism to M_n(k), or false and an injection of L into M_n(K)
//such that the image of L is stable by multiplication.
EnvelopingAlgebra := function(L)
  K, LK, HK, bc_map := BaseChangeAndSplitCartan(L);
  NL, Liso := NormaliseSplitLieAlgebra(LK, HK);
  assert false;
  _, n := IsSquare(Dimension(L));
  iso := bc_map * Liso;
  Ma := MatrixAlgebra(K, n);
  iso := map<L -> Ma | b :-> Ma!Eltseq(b @ iso)>;
  assert IsLieHom(iso, L);
  if K eq BaseRing(L) then
  	return true, iso;
  end if;
  Ass, phi := Algebra(Ma);
  RAss, res := MyRestrictionOfScalars(Ass, BaseRing(L));
  iso := iso * phi * res;
  return false, iso;
  //_, adjustment := AdjustStructureConstants(L, iso);
  //return false, iso * adjustment;
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
	return phi * psi;
end function;
