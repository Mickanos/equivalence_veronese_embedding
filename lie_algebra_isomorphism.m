/*****************************************************************
*                      Lie Algebra Isomorphisms					 *
*****************************************************************/

/*
	Computing isomorphisms to specific Lie algebras such as gl_n and
	(gl_n / k I_n) \oplus k.
*/

forward EnvelopingAlgebra;
forward IsomorphismToMnk;
forward IsomorphismToGlnModIn;

/*
	Computes an isomorphism to gl_n, if it exists.
	Inputs:
	- L: The domain of the isomorphism.
*/
IsomorphismToGln := function(L)
	k := BaseRing(L);
	_, n := IsSquare(Dimension(L));
	gln := MatrixLieAlgebra(k, n);
	done, phi := EnvelopingAlgebra(L);
	A := Codomain(phi);
	if done then
		psi := map<A -> A | x :-> x>;
	else
		psi := IsomorphismToMnk(A);
	end if;
	M := Matrix([Vector(b @ phi @ psi): b in Basis(L)]);
	iM := M^-1;
	return map<L -> gln |
		x :-> gln!Eltseq(Vector(x) * M), y :-> L!Eltseq(Vector(y) * iM)>;
end function;

/*
	Computes an isomorphism to (gl_n / k I_n) \oplus k if it exists.
	Inputs:
		- L: The domain of the isomorphism.
		- inj_ext: The output of the same name from ConstructNotGln.
		- proj_gln: Likewise.
*/
IsomorphismToNotGln := function(L, inj_ext, proj_gln)
	summands := DirectSumDecomposition(L);
	target := Codomain(inj_ext);
	one_target := Basis(target)[1];
	C := [g : g in summands | Dimension(g) eq 1][1];
	one_domain := L!Basis(C)[1];
	g := [g : g in summands | Dimension(g) ne 1][1];
	iso_g := IsomorphismToGlnModIn(g, proj_gln);
	return hom<L -> target | [<L!a, a @ iso_g @ inj_ext> : a in Basis(g)]
							cat [<one_domain, one_target>]>;
end function;

/*
	Compute the roots and corresponding spaces of the adjoint representation 
	of a split Cartan subalgebra H on L.
	Inputs:
		- L: The domain of the isomorphism.
		- H: A split Cartan subalgebra of L.
	Outputs:
		- spaces: The sequence of eigenspaces of H.
		- roots: The sequence of roots of H, in order matching that of spaces.
*/
ComputeRoots := function(L, H)
	mats := [Matrix(-AdjointMatrix(L, h)) : h in Basis(H)];
	spaces, roots := CommonEigenspaces(mats);
	roots := [Vector(r) : r in roots];
	i := Index(roots, Parent(roots[1])!0);
	Remove(~spaces, i);
	Remove(~roots, i);
	return spaces, roots;
end function;

/*
	Computes the privileged basis of an eigenspace of the adjoint representation
	of a split Cartan subalgebra of a Lie algebra g isomorphic to gl_n,
	following Lemma 5.9 of the publication.
	Inputs:
		- L: The Lie algebra isomorphic to gl_n.
		- spaces: The sequence of eigenspaces of L under the Cartan subalgebra.
		- roots: The sequence of roots, ordered accordingly.
		- i: The index of the space whose privileged basis is to be computed.
*/
Char2SpaceBreak := function(L, spaces, roots, i)
	F := BaseRing(L);
	root := roots[i];
	space := spaces[i];
	j := Index([j ne i and (r + root) in roots : j -> r in roots], true);
	k := Index(roots, root + roots[j]);
	pivot_space := spaces[j];
	target_space := spaces[k];
	ba := Basis(space);
	mats := [
		Matrix([
			Coordinates(target_space, Vector(a*L!v))
		: v in Basis(pivot_space)])
	: a in ba];
	a := mats[1];
	b := mats[2];

	mid := a[1,1]*b[2,2] + a[2,2]*b[1,1] - a[1,2]*b[2,1] - a[2,1]*b[1,2];
	da := Determinant(a);
	db := Determinant(b);
	R := PolynomialRing(F);
	if IsZero(da) then
		return [L!ba[1], IsZero(db)
			select L!ba[2]
			else L!(ba[1]) - mid/db * ba[2]];
	end if;
	zeros := [t[1] : t in Roots(R![db, mid, da])];
	assert #zeros eq 2;
	return [L!(z*ba[1] + ba[2]) : z in zeros];
end function;

/*
	Computes a basis of eigenvectors of Lie algebra L isomorphic to gl_n under
	the adjoint representation of a split Cartan subalgebra. The basis is
	suitable to be used for computing an isomorphim to gl_n following
	Algorithm 5.10.
	Inputs:
		- L: The Lie algebra isomorphic to gl_n.
		- spaces: The sequence of eigenspaces of L under the Cartan subalgebra.
		- roots: The sequence of roots of L, ordered accordingly.
	Outputs:
		A sequence of sequences, so the eigenvectors are grouped by eigenspaces.
*/
Eigenbasis := function(L, spaces, roots)
	return [
		Dimension(space) eq 1 select [L!b : b in Basis(space)] else
		Char2SpaceBreak(L, spaces, roots, i)
		: i -> space in spaces];
end function;

/*
	Checks whether an object appears as a value in a dictionary. Linear cost.
	Inputs:
		- A: The dictionary.
		- v: The value to be checked.
*/
AppearsIn := function(A, v)
	return &or[A[k] eq v : k in Keys(A)];
end function;

/*
	Index the roots of the adjoint representation of a split Cartan subalgebra
	of a Lie algebra isomorphic to gl_n in a way that matches their respective
	eigenspaces with the eigenspaces of the representation of the representation
	of the canonical split Cartan subalgebra of gl_n.
	This is step 2 of Algorithm 5.10, see also Lemma 5.8 and the proof of
	Proposition 5.4.
	Inputs:
		- roots: The sequence of roots of the aforemenionned representation.
*/
IndexRoots := function(roots)
	n := Degree(roots[1]);
	res := AssociativeArray();
	res[<1,2>] := roots[1];
	res[<2,1>] := -roots[1];
	/*
		The loop invariant is that at the start of iteration i, all the roots 
		of the  form Phi_{kl} such that k < l <= i are properly indexed in res.
	*/
	for i in [2..n-1] do
		if i eq 2 then
			res[<i,i+1>] := [r : r in roots
			| res[<1,i>] + r in roots and not AppearsIn(res, r)][1];
		else
			res[<i,i+1>] := [r : r in roots
				| res[<1,i>] + r in roots 
				and not res[<1,2>] + r in roots 
				and not AppearsIn(res, r)][1];
		end if;
		res[<1,i+1>] := res[<1,i>] + res[<i,i+1>];
		res[<i+1,i>] := -res[<i,i+1>];
		res[<i+1,1>] := -res[<1,i+1>];
		for j in [2..i-1] do
			res[<j,i+1>] := res[<1, i+1>] - res[<1,j>];
			assert res[<j, i+1>] in roots;
			res[<i+1,j>] := -res[<j,i+1>];
		end for;
	end for;
	return res;
end function;

//Returns scalar t such that t*a eq b;
//Throws an error if a and b aren't colinear vectors.
/*
	Computes scalar t such that t*a eq b, and throws an error if there is no
	such t.
	Inputs:
		- a: An indexable type that can be converted to a sequence.
		- b: Likewise.
*/
Colinearity := function(a, b)
  i := Index([IsZero(c) : c in Eltseq(a)], false);
  t := b[i]/a[i];
  assert t*a eq b;
  return t;
end function;

/*
	Computes a basis of a Lie algebra isomorphic to gl_n, so that mappring the
	basis elements to the canonical row-major basis of gl_n is an isomorphism
	of Lie algebras.
	Inputs:
		- roots: The sequence of roots of the Lie algebra under H.
		- indexed_roots: The roots as indexed by the function IndexRoots.
		- eigenbasis: An eigenbasis as computed by the function Eigenbasis.
		- H: The split Cartan Lie algebra.
*/
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
				res[<j,i+1>] := [e
					: e in eigenbasis[ell] | not IsZero(res[<1,j>] * e)][1];
				res[<i+1,j>] := [e
					: e in eigenbasis[ell] | e ne res[<j,i+1>]][1];
			end for;
			ell := Index(roots, indexed_roots[<1,i+1>]);
			res[<i+1,1>] := [e
				: e in eigenbasis[ell] | not IsZero(res[<2,i+1>] * e)][1];
			res[<1,i+1>] := [e
				: e in eigenbasis[ell] | e ne res[<i+1,1>]][1];
		end for;
	end if;

	//Now, to find e_1_1.

	total_space := Module(L);
	bad_space := sub<total_space |
		[Vector(res[<i,i+1>] * res[<i+1, i>]): i in [1..n-1]]>;
	system := Transpose(Matrix([indexed_roots[<i,i+1>]: i in [1..n-1]]));
	sol, nullspace := Solution(system,
							   Vector([One(k)] cat [Zero(k) : _ in [1..n-2]]));
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
		target := Vector([1] cat
						 [0 : _ in [1..N]] cat
						 Eltseq((total_space!res[<1,1>]) @ proj));
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

/*
	Outputs a copy of a Lie algebra, with basis changed to match the row-major
	canonical basis of gl_n, as well as the base-change isomorphism.
	Inputs:
		- L: The Lie algebra.
		- H: A split Cartan subalgebra of L.
*/
NormaliseSplitLieAlgebra := function(L, H)
	spaces, roots := ComputeRoots(L, H);
	eigenbasis := Eigenbasis(L, spaces, roots);
	indexed_roots := IndexRoots(roots);
	basis := GetNormalisedBasis(roots, indexed_roots, eigenbasis, H);
	return ChangeBasis(L, basis);
end function;

/*
	Computes a split Cartan subalgebra of a Lie algebra. May need to extend the
	scalars.
	Inputs:
		- L: The Lie algebra.
	Outputs:
		- K: An extension of the base field of L.
		- LK: The Lie algebra L if scalars extended to K.
		- HK: A split Cartan subalgebra of LK.
		- base_change_map: The natural map from L to LK.
*/
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

/*
	Given a polynomial P defined over an extension K/k, computes a
	sequence of polynomials over k, whose respective coefficients are the
	components of the coefficients of P with respect to some arbitrary k-basis
	of K.
	Inputs:
		- P: A polynomial defined over an extension of k.
		- k: A field.
*/
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

/*
	Computes an isomorphim f to gl_n(K) such that the images by f of the basis
	of its domain have characteristic polynomials with coefficients lying in k,
	the base ring of K.
	See Step 5 of Algorithm 5.2 and the proof of Theorem 1.1.
	Inputs:
		- iso: An isomorphism from some Lie algebra to gl_n(K).
	Output:
		- An isomorphism from the same Lie algebra to gl_n(K) with the property
			described above.
*/
AdjustStructureConstants := function(iso)
	MA := Codomain(iso);
	K := BaseRing(MA);
	L := Domain(iso);
	k := BaseRing(L);
	d := Degree(K, k);
	R := PolynomialRing(K, d);
	Rk := PolynomialRing(k, d);
	SeqSet := Parent([Rk.1]);
	lambda := &+[b * R.i : i-> b in Basis(K, k)];
	matrices := [ChangeRing(b @ iso, R) : b in Basis(L)];
	char_polys := [CharacteristicPolynomial(M): M in matrices];
	t := Parent(char_polys[1]).1;
	evals := [Evaluate(P, t - lambda * Trace(matrices[i])):
		i -> P in char_polys];
	coefficients := &cat[Coefficients(e): e in evals];
	polys_k := &cat[SeqSet | Polyseq(P, k)[2..d] : P in coefficients];
	X := Spec(quo<Rk | polys_k>);
	repeat
		lambda := K!Eltseq(Random(X(k)));
	until Degree(MA) * lambda ne -1;
	adjustment := map<MA -> MA | M :-> M + lambda * Trace(M) * One(MA)>;
	return iso * adjustment;
end function;
	
/*
	Outputs an associative algebra defined over k, with the same structure
	constants as A, which may be defined over an extension of K but has
	rational structure constants.
	Inputs:
		- A: An associative algebra with structure constants lying in k.
		- k: A subfield of the base ring of A.
*/
DescendAssociativeAlgebra := function(A, k)
	d := Dimension(A);
	Q := [[ChangeUniverse(Eltseq(BasisProduct(A, i, j)), k): j in [1..d]]:
		i in [1..d]];
	return AssociativeAlgebra<k, d | Q : Check := false>;
end function;

/*
	Computes a map from Lie algebra L to an associative algebra isomorphic
	to M_n(k). The map is an isomorphism of Lie algebras.
	Inputs:
		- L: The Lie algebra.
	Outputs:
		- A boolean indicating whether the codomain of the map is M_n(k) itself 
		or only isomorphic to it.
		- The map that was computed.
*/
EnvelopingAlgebra := function(L)
  K, LK, HK, bc_map := BaseChangeAndSplitCartan(L);
  NL, Liso := NormaliseSplitLieAlgebra(LK, HK);
  _, n := IsSquare(Dimension(L));
  iso := bc_map * Liso;
  Ma := MatrixAlgebra(K, n);
  if K eq BaseRing(L) then
  	M := Matrix([Eltseq(b @ iso): b in Basis(L)]);
	iM := M^-1;
	iso := map< L -> Ma |
		x :-> Ma!Eltseq(Vector(x) * M), y :-> L!Eltseq(Vector(y) * iM)>;
  	return true, iso;
  end if;
  iso := map<L -> Ma | b :-> Ma!Eltseq(b @ iso)>;
  iso := AdjustStructureConstants(iso);
  MaAss, phi := Algebra(Ma);
  A := sub<MaAss | [b @ iso @ phi: b in Basis(L)]>;
  A, psi := ChangeBasis(A, [b @ iso @ phi: b in Basis(L)]);
  B := DescendAssociativeAlgebra(A, BaseRing(L));
  final_iso := hom<L -> B | Basis(B)>;
  return false, final_iso;
end function;

/*
	Computes an isomorphism to the Lie algebra gl_n / k I_n.
	Inputs:
		- L: A Lie algebra isomorphic to gl_n / k I_n.
		- proj: The projection from gl_n to gl_n / k I_n.
*/
IsomorphismToGlnModIn := function(L, proj)
	k := BaseRing(L);
	if IsZero(k!(Dimension(L) + 1)) then
		e, lift := NontrivialCentralExtension(L);
	else
		e := DirectSum(L, AbelianLieAlgebra(k, 1));
		lift := hom<L -> e | Basis(e)[1..Dimension(L)]>;
	end if;
	iso := IsomorphismToGln(e);
	gln_mod_In := Codomain(proj);
	basis_image := [b @ lift @ iso @ proj: b in Basis(L)];
	return hom<L -> gln_mod_In | basis_image>;
end function;

/*
	Computes an isomorphism from an associative algebra to M_n(k).
	Inputs:
		- A: An associative algebra isomorphic to M_n(k).
*/
IsomorphismToMnk := function(A)
  _, n := IsSquare(Dimension(A));
  k := BaseField(A);
  MA := MatrixAlgebra(k, n);
  I := MinimalRightIdeals(A : Limit := 1)[1];
  return map<A -> MA | a :-> Matrix([Coordinates(I, e*a): e in Basis(I)])>;
end function;
