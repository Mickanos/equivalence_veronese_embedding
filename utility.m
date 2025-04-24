//Returns scalar t such that t*a eq b;
//Throws an error if a and b aren't colinear vectors.
Colinearity := function(a, b)
  i := Index([IsZero(c) : c in Eltseq(a)], false);
  t := b[i]/a[i];
  assert t*a eq b;
  return t;
end function;

//Input: a field k and a matrix M with coefficients in an extension K/k.
//Output: a matrix with coefficients in k, representing the same map as k-linear
//instead of K-linear. The basis of K as an extension of k is used to produce
//a k-basis of the domain and codomain of M.
MatrixRestrictionOfScalars := function(k, M)
    K := BaseRing(M);
    Rows := [b*r : b in Basis(K, k), r in Rows(M)];
    LongRows := [&cat[Eltseq(c, k): c in Eltseq(r)]: r in Rows];
    return Matrix(LongRows);
end function;

SplitMatrixAlgebra := function(A)
  _, n := IsSquare(Dimension(A));
  k := BaseField(A);
  MAlg := MatrixAlgebra(k, n);
  MAss, phi := Algebra(MAlg);
  I := MinimalRightIdeals(A : Limit := 1)[1];
  Mats := [Matrix([e*a: e in Basis(I)]): a in Basis(A)];
  return hom<A -> MAss | [M @ phi: M in Mats]> * Inverse(phi);
end function;