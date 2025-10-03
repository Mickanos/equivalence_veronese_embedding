// Useful auxiliary functions for Grassmannians and secants
// (e.g., for running the experiment reported in Remark 6.3)

Grassmannian := function(F, k, n)
  // returns equations for G(k, n) parametrizing k-dimensional
  // subspaces of an n-dimensional vector space over a field F
  // via the Plücker embedding (the equations are just the
  // Plücker relations)
  S := SetToSequence(Subsets({1..n}, k));
  d := #S;
  R := PolynomialRing(F, d);
  plucker := [];
  for i in Subsets({1..n}, k - 1) do
    for j in Subsets({1..n}, k + 1) do
      plucker_rel := R ! 0;
      for l in [1..k+1] do
        j_l := SetToSequence(j)[l];
        set_i := i join {j_l};
        if #set_i eq k then
          set_j := j diff {j_l};
          var_i := Index(S, set_i);
          var_j := Index(S, set_j);
          sign := (-1)^(l + k - Index(SetToSequence(set_i), j_l));
          plucker_rel +:= sign*R.var_i*R.var_j;
        end if;
      end for;
      if plucker_rel ne 0 then
        plucker cat:= [plucker_rel];
      end if;
    end for;
  end for;
  // remove linear dependencies
  // for simplicity MinimalBasis is used, but this may become
  // too slow, so only useful for toy examples
  return MinimalBasis(Ideal(plucker));
end function;

SecGrass := function(F, n)
  // returns equations for Sec(G(2, n)) over F using the description
  // in terms of Pfaffians stated in Di Tullio -- Gyawali; this is
  // much more efficient than via the Magma intrinsic SecantVariety
  d := Binomial(n, 2);
  R := PolynomialRing(F, d);
  M := ZeroMatrix(R, n, n);
  counter := 0;
  for i in [1..n] do for j in [i+1..n] do
  counter +:= 1;
    M[i][j] := R.counter;
    M[j][i] := -R.counter;
  end for; end for;
  return Pfaffians(M, 6);
end function;

PolToVector := function(f, mons)
  F := BaseRing(Parent(f));
  N := #mons;
  w := [F ! 0 : i in [1..N]];
  coeffs_f := Coefficients(f);
  mons_f := Monomials(f);
  for r in [1..#coeffs_f] do
    w[Index(mons, mons_f[r])] := coeffs_f[r];
  end for;
  return w;
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
  W := sub<V | [PolToVector(f, mons) : f in pols] >;
  U, Quo := quo<V | W>;
  r := Dimension(U);
  basis := Basis(MatrixAlgebra(F, n));
  M := [];
  for b in basis do
    for f in pols do
      M cat:= Eltseq(Quo(PolToVector(&+[&+[b[i][j]*R.j*Derivative(f, i) : j in [1..n]] : i in [1..n]], mons)));
    end for;
  end for;
  M := Matrix(n^2, #pols*r, M);
  M := HorizontalJoin(M, Matrix(n^2, 1, [Trace(b) : b in basis])); // trace 0 part
  B := Basis(Nullspace(M));
  MatBasis := [Matrix(F,n,n,Eltseq(b)): b in B];
  ALie := sub<MatrixLieAlgebra(F, n) | MatBasis>;
  L, phi := LieAlgebra(ALie);
  return L, Inverse(phi);
end function;

function QuadricToMatrix(Q);
  // RETURNS THE SYMMETRIC MATRIX CORRESPONDING TO A
  // GIVEN QUADRATIC HOMOGENEOUS FORM OVER A FIELD OF
  // CHARACTERISTIC NOT TWO
  R := Parent(Q);
  n := Rank(R);
  F := BaseRing(R);
  M := Matrix(F,n,n,[0 : i in [1..n^2]]);
  for t in Terms(Q) do
    exps := Exponents(t);
    coef := Coefficients(t)[1];
    i := Index(exps,2);
    if i eq 0 then
      i := Index(exps,1);
      j := Index(Remove(exps,i),1) + 1;
      M[i][j] := coef/2; M[j][i] := coef/2;
    else M[i][i] := coef;
    end if;
  end for;
  return M;
end function;

ComputeLieAlgebra := function(A)
  F := BaseRing(A[1]);
  n := Nrows(A[1]);
  AMod, Quo := quo<KMatrixSpace(F, n, n) | A>;
  M := HorizontalJoin(
    HorizontalJoin([Matrix([Eltseq(Quo(Transpose(b)*a + a*b)) :
    b in Basis(MatrixAlgebra(F,n))]): a in A]),
    Matrix(F, n^2, 1, [Trace(b) : b in Basis(MatrixAlgebra(F,n))]));
  M := Transpose(M);
  RemoveZeroRows(~M);
  M := Transpose(M);
  B := Basis(Nullspace(M));
  MatBasis := [Matrix(F,n,n,Eltseq(b)): b in B];
  ALie := sub<MatrixLieAlgebra(F, n) | MatBasis>;
  L, phi := LieAlgebra(ALie);
  return L, Inverse(phi);
end function;

// some test code for computing the Lie algebra of Grassmannians

p := NextPrime(10^5);
Fp := GF(p);

print "---";

for k in [2..3] do for n in [2*k..2*k+1] do
  print "Dimension of the Lie algebra of the Grassmannian Gr(", k, ",", n, ")";
  print Dimension(ComputeLieAlgebra([QuadricToMatrix(f) : f in Grassmannian(Fp, k, n)]));
end for; end for;

print "---";

for n in [6..9] do
  print "Dimension of Sec(Gr(2,", n, "))";
  print Dimension(ComputeLieAlgebraHomogeneous(SecGrass(Fp, n)));
end for;
