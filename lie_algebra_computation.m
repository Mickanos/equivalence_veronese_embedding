forward ComputeLieAlgebraBasis;
forward ComputeLieAlgebraBasisHomogeneous;

ComputeLieAlgebra := function(eqs)
  R := Parent(eqs[1]);
  k := BaseRing(R);
  N := Rank(R);
  gln := MatrixLieAlgebra(k, N);

  if IsZero(k!2) then
    basis := ComputeLieAlgebraBasisHomogeneous(eqs);
  else
    basis := ComputeLieAlgebraBasis(eqs);
  end if;

  ChangeUniverse(~basis, gln);

  s, inj := sub<gln | basis>;
  g, conv := LieAlgebra(s);
  return g, Inverse(conv) * inj;
end function;

ComputeLieAlgebraBasis := function(eqs)
  eqs := [SymmetricMatrix(e): e in eqs];
  F := BaseRing(eqs[1]);
  n := Nrows(eqs[1]);
  AMod, Quo := quo<KMatrixSpace(F, n, n) | eqs>;
  M := HorizontalJoin([Matrix([Eltseq(Quo(Transpose(b)*a + a*b)) :
      b in Basis(MatrixAlgebra(F,n))]): a in eqs]);
  M := Transpose(M);
  RemoveZeroRows(~M);
  M := Transpose(M);
  B := Basis(Nullspace(M));
  return [Matrix(F,n,n,Eltseq(b)): b in B];
end function;

PolyToVector := function(P, mons)
	return Vector([MonomialCoefficient(P, m) : m in mons]);
end function;

ComputeLieAlgebraBasisHomogeneous := function(pols)
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
  res := [Matrix(F,n,n,Eltseq(b)): b in B];
  return res;
end function;