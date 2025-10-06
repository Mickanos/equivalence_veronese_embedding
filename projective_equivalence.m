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
  return L, Inverse(phi);
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
    M_r := Codomain(g_to_gln);
    M_N := Codomain(natural_rep);
    tau := map< M_r -> M_r | x :-> -Transpose(x)>;
    if not IsZero(k!n) and not IsZero(k!d) then
	    c := Basis(Center(g))[1];
	    a := (c @ g_to_gln)[1,1];
	    b := (c @ natural_rep)[1,1];
	    h_t := map< M_r -> M_r | x :-> x + (b/(a*d) - 1)/n * Trace(x) * One(M_r)>;
	    h_min_t := map< M_r -> M_r | x :-> x + (-(b/(a*d) + 1)/n) * Trace(x) * One(M_r)>;
    else
    h_t := map< M_r -> M_r | x :-> x>;
    h_min_t := map< M_r -> M_r | x :-> x>;
    end if;
    return [<Matrix(b @ natural_rep),
        b @ g_to_gln @ h_t @ veronese_rep ,
        b @ g_to_gln @ h_min_t @ tau @ veronese_rep>: b in Basis(g)];
end function;

//Takes two isomorphic Lie algebras embedded in gl_n.
//They should be represented as one list of triples of matrices
//corresponding to respective basis elements of each Lie algebras
//that are images of one another by a Lie algebra isomorphism.
//Elements two and three are conjugate by the outer automorphism of gl_n.
//Outputs an isomorphism of the natural representation. That is,
//an invertible matrix T in gl_n such that the second Lie algebra is the
//conjugate of the first by T.
LieAlgebraRepresentationIsomorphism := function(triples: verbose := false)
    Mat := Parent(triples[1][1]);
    system := Matrix([&cat[Eltseq(p[1]*e - e*p[2]): p in triples] :
        e in Basis(Mat)]);
    target_rank := Dimension(Mat) - 1;
    if verbose then
        print "We compute an isomorphism of representations.";
    end if;
    if Rank(system) eq target_rank then
        K := Basis(Nullspace(system));
    else
        if verbose then
            print "We failed to find one. We must precompose our isomorphism";
            print "of Lie algebras with the outer automorphism of sl_n.";
            print "We get the following mapping:";
            for t in triples do
                printf "The matrix \n%o\n is sent to\n%o\n", t[1], t[3];
            end for;
        end if;
    	system := Matrix([&cat[Eltseq(p[1]*e - e*p[3]): p in triples] :
	    e in Basis(Mat)]);
        K := Basis(Nullspace(system));
    end if;
    k := BaseRing(triples[1][1]);
    r := NumberOfRows(triples[1][1]);
    T := Matrix(k,r,r,Eltseq(K[1]));
    if verbose then
        print "We solve the system of linear equations and find that the ";
        printf "matrix\n%o\n is a projective equivalence of varieties.\n", T;
    end if;
    return T;
end function;


//Given quadric equations for a projective variety, computes a projective
//Equivalence to the Veronese embedding of degree d with n variables.
EquivalenceToVeronese := function(n, d, eqs : f := 1, verbose := false)
        g, natural_rep := ComputeLieAlgebra(eqs , n: f := f, verbose := verbose);
    lie_isom := VeroneseLieAlgebraIsom(g,
        natural_rep,
        n,
        d :
        verbose := verbose);
    return LieAlgebraRepresentationIsomorphism(lie_isom: verbose := verbose);
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
