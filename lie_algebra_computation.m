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
  The computation may be optimised if the base field has odd characteristic.
  Inputs:
    - eqs : A sequence of homoegenous polynomial.
    - optimise : Flag to toggle an optimisation of the computation.
    - n : The dimension of the variety. Only required if optimise is true.
    - d : The degree of the Veronese variety. Only required if optimise is true.
*/
ComputeLieAlgebra := function(eqs : optimise := true, n := 0, d := 0)
  R := Parent(eqs[1]);
  k := BaseRing(R);
  N := Rank(R);
  gln := MatrixLieAlgebra(k, N);

  if IsZero(k!2) then
    basis := ComputeLieAlgebraBasisHomogeneous(eqs);
    if optimise then
      print "Optimisation of the computation of lie algebra not implemented in \
characteristic 2.";
    end if;
  else
    eqs := [SymmetricMatrix(e): e in eqs];
    if optimise then
      try
        f := lie_computation_proportions[<n, d>];
      catch e
        printf "Optimisation data not computed for n = %o, d = %o.\nRunning the\
 unoptimised computation.", n, d;
        f := 1;
      end try;
    else
      f := 1;
    end if;
    basis := ComputeLieAlgebraBasis(eqs :
                                    f := f,
                                    expected_dimension := (n + 1)^2);
  end if;

  ChangeUniverse(~basis, gln);

  s, inj := sub<gln | basis>;
  g, conv := LieAlgebra(s);
  return g, Inverse(conv) * inj;
end function;

/*
  Computes a random subsequence of L of size n.
  Inputs:
    - L : A sequence.
    - n : A nonnegative integer.
*/
RandomElements := function(L, n)
  s := #L-1;
  res := {};
  repeat
    Include(~res, Random(s) + 1);
  until #res eq n;
  return [L[i] : i in res];
end function;

/*
  Computes the basis of the Lie algebra of a projective quadric.
  Only works in odd characteristic.
  The computation may be optimised by only using a randomly sampled small 
  proportion of the equations of the projective variety when computing 
  the basis of the Lie algebra.
  Inputs:
    - eqs: A sequence of homogeneous polynomials of degree 2.
    - f: The proportion parameter for optimising the computation.
    - expected_dimension: The expected dimension of the Lie algebra. Only
      required if f is not 1.
*/
ComputeLieAlgebraBasis := function(eqs : f := 1, expected_dimension := 0)
  F := BaseRing(eqs[1]);
  n := Nrows(eqs[1]);
  MS := KMatrixSpace(F, n, n);
  AMod, Quo := quo<MS | eqs>;
  if f lt 1 then
    number_eqs_used := Ceiling(f * #eqs);
    repeat
      used_eqs := RandomElements(eqs, number_eqs_used);
      M := HorizontalJoin([Matrix([Eltseq(Quo(Transpose(b)*a + a*b)) :
          b in Basis(MS)]): a in used_eqs]);
      M := Transpose(M);
      RemoveZeroRows(~M);
      M := Transpose(M);
      ker := Nullspace(M);
    until Dimension(ker) eq expected_dimension;
  else
    M := HorizontalJoin([Matrix([Eltseq(Quo(Transpose(b)*a + a*b)) :
      b in Basis(MS)]): a in eqs]);
    M := Transpose(M);
    RemoveZeroRows(~M);
    M := Transpose(M);
    ker := Nullspace(M);
  end if;
  B := Basis(ker);
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