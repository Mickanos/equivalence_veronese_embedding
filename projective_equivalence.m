//Computes the Lie algebra of the Veronese embedding of degree d (with n vars).
//Note that it is a homomorphism of Lie algebras. However, we output a map
// between Matrix algebras for practical reasons.
LieAlgebraVeroneseEmbedding := function(k, n, d)
    R := PolynomialRing(k, n);
    mons := SetToSequence(MonomialsOfDegree(R, d));
    op := [[map<R -> R | p :-> R.j * Derivative(p,i)>: j in [1..n]]:
        i in [1..n]];
    Mats := [[Matrix(
        k,
        [[MonomialCoefficient(im, col) : col in mons]
            where im is mon @ op[i][j]: mon in mons]
        ): j in [1..n]]: i in [1..n]];
    Mn := MatrixAlgebra(k, n);
    Mr := MatrixAlgebra(k, #mons);
    return map< Mn -> Mr | M :-> &+[M[i,j] * Mats[i][j]: i,j in [1..n]]>, mons;
end function;

// *******************************
// ** COMPUTING THE LIE ALGEBRA **
// *******************************

// input: n x n matrices A1, ..., At
// output: The Lie algebra of square matrices X such that
// X^t*Ai + Ai*X is contained in <A1, ..., At> for all i

ComputeLieAlgebra := function(eqs, r : f := 1, verbose := false)
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
    B := Basis(Nullspace(M));
    count +:=1;
    if IsDivisibleBy(count, 5) then
        printf "Warning: already %o tries and the Lie algebra could not", count;
        print " be computed.";
    end if;
  until #B eq r^2;
  printf "Lie algebra computed in %o tries.\n", count;
  MatBasis := [Matrix(F,n,n,Eltseq(b)): b in B];
  if verbose then
    print "We found a basis for the Lie algebra of the variety. Is is:";
    print MatBasis;
  end if;
  ALie := sub<MatrixLieAlgebra(F, n) | [MyLieBracket(a, b) : a, b in MatBasis]>;
  L, phi := LieAlgebra(ALie);
  ZeroTrace := Matrix([[Trace(AdjointMatrix(L,a))] : a in Basis(L)]);
  ZTBasis := [L!b : b in Basis(Nullspace(ZeroTrace))];
  res, psi := sub<L | ZTBasis>;
  return res, Inverse(phi * psi);
end function;


//Given quadratic equations for a projective variety, find an isomorphism
//to the Lie algebra of the Veronese embedding.
//Outputs a list of triples of equivalent basis elements of the Lie algebras
//respectively of the given variety and of the Veronese embedding.
//The third element of the tuple is the same equivalence precomposed
//by negative transpose in sln.
VeroneseLieAlgebraIsom := function(n, d, eqs : f := 1, verbose := false)
    Quads := [QuadricToMatrix(e) : e in eqs];
    k := BaseRing(Quads[1]);
    g, natural_rep := ComputeLieAlgebra(Quads, n: f := f, verbose := verbose);
    g_to_sln := SplitSln(g);
    if verbose then
        print "We have computed a splitting of the Lie algebra.";
        for b in Basis(g) do
            printf "The matrix \n%o\n is sent to\n", b @ natural_rep;
            print (b @ g_to_sln);
        end for;
    end if;
    veronese_rep := LieAlgebraVeroneseEmbedding(k, n, d);
    if verbose then
        print "Now, composing the previous map with the Veronese embedding, ";
        print "we get the following correspondences:";
        for b in Basis(g) do
            printf "The matrix \n%o\n is sent to\n", b @ natural_rep;
            print (b @ (g_to_sln * veronese_rep));
        end for;
    end if;
    return [<Matrix(b @ natural_rep),
        b @ (g_to_sln * veronese_rep ),
        Transpose(-b @ g_to_sln) @ veronese_rep>: b in Basis(g)];
end function;

//Takes two isomorphic Lie algebras embedded in gl_n.
//They should be represented as one list of pairs of matrices
//corresponding to respective basis elements of each Lie algebras
//that are images of one another by a Lie algebra isomorphism.
//Outputs an isomorphism of the natural representation. That is,
//an invertible matrix T in gl_n such that the second Lie algebra is the
//conjugate of the first by T.
LieAlgebraRepresentationIsomorphism := function(triples: verbose := false)
    Mat := Parent(triples[1][1]);
    system := Matrix([&cat[Eltseq(p[1]*e - e*p[2]): p in triples] :
        e in Basis(Mat)]);
    K := Basis(Nullspace(system));
    if verbose then
        print "We compute an isomorphism of representations.";
    end if;
    if IsEmpty(K) then
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
    lie_isom := VeroneseLieAlgebraIsom(n, d, eqs : f := f, verbose := verbose);
    return LieAlgebraRepresentationIsomorphism(lie_isom: verbose := verbose);
end function;
