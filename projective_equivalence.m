
// *******************************
// ** COMPUTING THE LIE ALGEBRA **
// *******************************

//Input: A sequence of homogeneous polynomial equations for a projective variety X in P^N.

ComputeLieAlgebra := function(eqs)
	//In practice for now, we only get quadrics so there is no need to sort out the degrees.
	G, space,  mons := FreeHomogeneousPolys(eqs);
	R := Parent(eqs[1]);
	N := Rank(R);
	k := BaseRing(R);
	P := Transpose(BasisMatrix(space));
	F := Nullspace(P);
	forms := Transpose(BasisMatrix(F));
	assert &and[IsZero((f, s)) : f in Basis(F), s in Basis(space)];
	sys := Matrix([
			&cat[Eltseq(PolyToVector(R.i * Derivative(e, j), mons) * forms) : e in eqs]
		: i, j in [1..N]]);
	basis := [Matrix(k, N, N, Eltseq(v)): v in Basis(Nullspace(sys))];
	MA := MatrixLieAlgebra(k, N);
	g := sub<MA | basis>;
	g, map := LieAlgebra(g);
	natural_rep := map<g -> MatrixAlgebra(k, N) | x :-> Matrix(x @@ map)>;
	return g, natural_rep;
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
    c := Basis(Center(g))[1];
    N := Degree(Codomain(natural_rep));
    M_r := Codomain(g_to_gln);
    M_N := Codomain(natural_rep);
    M := (c @ natural_rep) - ((c @ g_to_gln) @ veronese_rep);
    t := Colinearity(Vector(One(M_N)), Vector(M));
    g_to_gln := g_to_gln * map< M_r -> M_r | a :-> a + (t/d) * One(M_r)>;
    print c @ natural_rep;
    print c @ g_to_gln @ veronese_rep;
    return [<Matrix(b @ natural_rep),
        (b @ g_to_gln) @ veronese_rep ,
        Transpose(-b @ g_to_gln) @ veronese_rep>: b in Basis(g)];
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
    if Rank(system) le target_rank then
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
    g, natural_rep := ComputeLieAlgebra(eqs);
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
