// *******************************
// ** COMPUTING THE LIE ALGEBRA **
// *******************************

ComputeLieAlgebra := function(eqs, r : f := 1, verbose := false)
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
  MatBasis := [Matrix(F,n,n,Eltseq(b)): b in B];
  if verbose then
    print "We found a basis for the Lie algebra of the variety. Is is:";
    print MatBasis;
  end if;
  ALie := sub<MatrixLieAlgebra(F, n) | MatBasis>;
  L, phi := LieAlgebra(ALie);
natural_rep := map<L -> MatrixAlgebra(F, n) | a :-> Matrix(a @@ phi)>;
  return L, natural_rep;
end function;

ComputeLieAlgebraHomogeneous := function(pols)
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
  MatBasis := [Matrix(F,n,n,Eltseq(b)): b in B];
  ALie := sub<MatrixLieAlgebra(F, n) | MatBasis>;
  L, phi := LieAlgebra(ALie);
  natural_rep := map<L -> MatrixAlgebra(F, n) | a :-> Matrix(a @@ phi)>;
  return L, natural_rep;
end function;


//Given the Lie algebra of a projective variety, find an isomorphism
//to the Lie algebra of the Veronese embedding.
//Outputs a list of triples of equivalent basis elements of the Lie algebras
//respectively of the given variety and of the Veronese embedding.
//The third element of the tuple is the same equivalence precomposed
//by negative transpose in sln.
VeroneseLieAlgebraIsom := function(g, natural_rep, n, d : verbose := false)
k := BaseRing(g);
g_to_gln := SplitGln(g);
	if verbose then
		print "We have computed a splitting of the Lie algebra.";
		for b in Basis(g) do
			printf "The matrix \n%o\n is sent to\n", b @ natural_rep;
			print (b @ g_to_gln);
		end for;
	end if;
	veronese_rep := LieAlgebraVeroneseEmbedding(k, n, d);
	if verbose then
		print "Now, composing the previous map with the Veronese embedding, ";
		print "we get the following correspondences:";
		for b in Basis(g) do
			printf "The matrix \n%o\n is sent to\n", b @ natural_rep;
			print (b @ (g_to_gln * veronese_rep));
		end for;
	end if;
	e := ElementaryMatrix(k, n, n, 1, 1);
	ev_nat := SetToSequence(Eigenvalues(e @@ g_to_gln @ natural_rep));
	ev_vero := SetToSequence(Eigenvalues(e @ veronese_rep));
	ev_1 := [a[1] : a in ev_nat | a[2] eq ev_vero[1][2]][1];
	ev_2 := [a[1] : a in ev_nat | a[2] eq ev_vero[2][2]][1];
	a := (ev_vero[2][1] - ev_vero[1][1])/(ev_2 - ev_1);
	b := ev_vero[1][1] - a * ev_1;
	c := (IdentityMatrix(k, n) @ veronese_rep)[1,1];
	iso := h_isom(k, n, -b/c);
	if not IsOne(a) then
		iso := tau_isom(k, n) * iso;
	end if;
	reps := [g_to_gln * iso * veronese_rep];
	if IsZero(k!2) then
		Append(~reps, g_to_gln * iso * tau_isom(k, n) * veronese_rep);
	end if;
	return natural_rep, reps;
end function;

//Takes two isomorphic Lie algebras embedded in gl_n.
//They should be represented as one list of triples of matrices
//corresponding to respective basis elements of each Lie algebras
//that are images of one another by a Lie algebra isomorphism.
//Elements two and three are conjugate by the outer automorphism of gl_n.
//Outputs an isomorphism of the natural representation. That is,
//an invertible matrix T in gl_n such that the second Lie algebra is the
//conjugate of the first by T.
LieAlgebraRepresentationIsomorphism := function(rep_1, reps : verbose := false)
    N := Degree(Codomain(rep_1));
    g := Domain(rep_1);
    k := BaseField(g);
    Mat := MatrixAlgebra(k, N);
    for rep_2 in reps do
	    system := Matrix([&cat[Eltseq((b @ rep_1)*e - e*(b @ rep_2)): b in Basis(g)] :
		e in Basis(Mat)]);
	    if Rank(system) ne NumberOfRows(system) then
	    	break;
	    end if;
    end for;
    if verbose then
        print "We compute an isomorphism of representations.";
    end if;
    T := Mat!Eltseq(Basis(Nullspace(system))[1]);
    if verbose then
        print "We solve the system of linear equations and find that the ";
        printf "matrix\n%o\n is a projective equivalence of varieties.\n", T;
    end if;
    return T;
end function;


//Given quadric equations for a projective variety, computes a projective
//Equivalence to the Veronese embedding of degree d with n variables.
EquivalenceToVeronese := function(n, d, eqs : f := 1, verbose := false)
	k := BaseRing(Parent(eqs[1]));
	if IsZero(k!2) then
		g, natural_rep := ComputeLieAlgebraHomogeneous(eqs);
	else
		g, natural_rep := ComputeLieAlgebra(eqs , n: f := f, verbose := verbose);
	end if;
	rep_1, reps := VeroneseLieAlgebraIsom(g,
		natural_rep,
		n,
		d :
		verbose := verbose);
	return LieAlgebraRepresentationIsomorphism(rep_1, reps : verbose := verbose);
end function;

//The same as above, but but assuming that the Lie algebra is already given.
EquivalenceFromLie := function(g, natural_rep, n, d : verbose := false)
    lie_isom := VeroneseLieAlgebraIsom(g,
        natural_rep,
        n,
        d :
        verbose := verbose);
    return LieAlgebraRepresentationIsomorphism(lie_isom: verbose := verbose);
end function;
