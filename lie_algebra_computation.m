/*****************************************************************
*                      Lie Algebra Computation                   *
*****************************************************************/

/*
  Computing the Lie algebra of a projective variety, given as a sequence
  of homogeneous polynomial equations.
  See Section 2.2 for the definition of the Lie algebra of a projective
  variety.
*/

forward ComputeLieAlgebraBasis;
forward ComputeLieAlgebraBasisHomogeneous;

/*
  Compute the Lie algebra of a projective variety.
  Inputs:
    - eqs : A sequence of homoegenous polynomial.
*/
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

/*
  Computes the basis of the Lie algebra of a projective quadric.
  Only works in odd characteristic.
  Inputs:
    - eqs: A sequence of homogeneous polynomials of degree 2.
*/
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

/*
  Turns a homogeneous multivariate polynomial into a vector.
  The coefficients are ordered following a given sequence of monomials
  generating the space.
  Inputs:
    - P: The polynomial.
    - mons: The basis of the space composed of monomials.
*/
PolyToVector := function(P, mons)
	return Vector([MonomialCoefficient(P, m) : m in mons]);
end function;

/*
  Computes the basis of the Lie algebra of a projective variety.
  Inputs:
    - eqs: A sequence of homogeneous polynomials.
*/
ComputeLieAlgebraBasisHomogeneous := function(pols)
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