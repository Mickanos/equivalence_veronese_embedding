/*****************************************************************
*                        Testing Helpers                         *
*****************************************************************/

/*
  Helper functions for testing purposes. These functions either generate
  inputs for the problems treated or check that solutions are valid.
*/

forward NumberOfMonomials;
forward GetVeroneseEquations;
forward PolySubstitution;

//Generate a variety by computing the image of a Veronese variety by
//a random automorphism of the ambient projective space.
/*
  Generates a F_q-variety that is projectively equivalent to the Veronese 
  variety of dimension n-1 and degree d.
  Inputs:
    - q: The order of the base field of the desired variety.
    - n: The dimension of the desired variety.
    - d: The degree of the isomorphic Veronese variety.
*/
GetTwistedVeronese := function(q, n, d)
  k := GF(q);
  vero_eqs := GetVeroneseEquations(k, n, d);
  N := Rank(Universe(vero_eqs));
  T := Random(GL(N, k));
  return [PolySubstitution(e, T) : e in vero_eqs];
end function;

/*
  Checks if a matrix describes a projective equivalence between two projecrtive
  varieties described by sequences of homogeneous polynomials.
  Inputs:
    - eqs_1, eqs_2: Sequences of homogeneous polynomials.
    - T: An invertible matrix of appropriate size.
*/
CheckProjectiveEquivalence := function(eqs_1, eqs_2, T)
  R := Universe(eqs_1);
  I_1 := ideal< R | [PolySubstitution(e, T) : e in eqs_1]>;
  I_2 := ideal< R | eqs_2>;
  return I_1 eq I_2;
end function;

/*
  Checks if a matrix describes a projective equivalence between a projective
  variety described by a sequence of homogeneous polynomials and the Veronese
  variety of dimension n-1 and degree d.
  Inputs:
    - eqs: The equations of the projective variety.
    - T: An invertible matrix of appropriate size.
    - n: The dimension of the varieties.
    - d: The degree of the Veronese variety.
*/
CheckEquivalenceToVeronese := function(eqs, T, n, d)
  k := BaseRing(Universe(eqs));
  eqs_vero := GetVeroneseEquations(k, n, d);
  return CheckProjectiveEquivalence(eqs, eqs_vero, T);
end function;

/*
  Computes a Lie F_q-algebra representation isomorphic to the representation
  attached to the Veronese variety of dimension n-1 and degree d.
  Inputs:
    - q: The size of the base field.
    - n: The dimension of the underlying variety.
    - d: The degree of the underlying Veronese variety.
  Outputs:
    - The Domain of the representation.
    - The representation.
*/
GetTwistedVeroneseRepresentation := function(q, n, d)
    k := GF(q);
    phi := VeroneseRepresentation(k, n, d);
    g := Domain(phi);
    glN := Codomain(phi);
    LieBasis := [Matrix(b @ phi) : b in Basis(g)];
    N := Degree(glN);
    T := Random(GL(N, k));
    Ti := T^-1;
    TwistedLieBasis := [T*b*Ti : b in LieBasis];
    S, inj := sub<glN | TwistedLieBasis>;
    L, psi := LieAlgebra(S);
    return L, Inverse(psi) * inj;
end function;

/*
  Applies the linear substitution described by a matrix to a polynomial.
  Inputs:
    - p: A polynomial.
    - M: A matrix.
*/
PolySubstitution := function(p, M)
  R := Parent(p);
  n := Rank(R);
  return Evaluate(p, [&+[r[i]*R.i : i in [1..n]]: r in Rows(M)]);
end function;

/*
  Computes a hamel basis of the space spanned by a sequence of homogeneous
  polynomials.
  Inputs:
    - L: A sequence of homogeneous polynomials.
*/
FreeHomogeneousPolys := function(L)
  i := 1;
  repeat
    d := Degree(L[i]);
    i +:= 1;
  until d ne -1;
  R := Parent(L[1]);
  mons := SetToSequence(MonomialsOfDegree(R, d));
  vectors := [Vector([MonomialCoefficient(P, m) : m in mons]): P in L];
  space := sub<Parent(vectors[1]) | vectors>;
  return [&+[v[i]*m : i->m in mons]: v in Basis(space)], space, mons;
end function;

/*
  Computes quadratic equations for the Veronese variety of dimension n-1 and
  degree d. The equations are defined over Z and are therefore valid for any
  base field.
  The computation could probably be optimised.
  Inputs:
    - n: The dimension of the desired variety.
    - d: The degree of the desired veronese variety.
*/
VeroneseEquations := function(n, d)
  Z := IntegerRing();
  R := PolynomialRing(Z, n + 1);
  mons := SetToSequence(MonomialsOfDegree(R, d));
  S := PolynomialRing(Z, #mons);
  mon_index := map< R -> { 1..#mons } | p :-> Index(mons, p)>;
  eqs := SetToSequence({
    S.((&*[R.i : i in s[1..d]]) @ mon_index) *
    S.((&*[R.i : i in s[d+1..2*d]]) @ mon_index) -
    S.((&*[R.i : i in s[1..d-1]] * R.(s[d+1])) @ mon_index) *
    S.((&*[R.i : i in s[d+2..2*d]] * R.(s[d])) @ mon_index) :
  s in Subsequences({1..(n + 1)},2*d)});
  return FreeHomogeneousPolys(eqs);
end function;

/*
  Computes equations for the Veronese variety of dimension n-1 and d, and
  saves them in the local file "veronese_equations.m".
  Make sure to run magma from the root directory of the project for consistency.
  Inputs:
    - n: The dimension of the desired variety.
    - d: The degree of the variety.
*/
PrecomputeVeroneseEquations := function(n, d)
  filename := "precomputed_data.m";
  eqs := VeroneseEquations(n, d);
  R := Universe(eqs);
  N := Rank(R);
  AssignNames(~R, [Sprintf("R.%o", i): i in [1..N]]);
  s := Sprintf("veronese_%o_%o := function()\n  R := PolynomialRing(\
IntegerRing(), %o);\n  return %o;\nend function;\n", n, d, N, eqs);
  PrintFile(filename, s);
  return eqs;
end function;

/*
  Outputs equations for the Veronese k-variety of dimension n - 1 and degree d,
  assuming that these equations are saved in the file "veronese_equations.m"
  Inputs:
    - k: The base field.
    - n: The dimension of the desired variety.
    - d: The degree of the variety.
*/
GetVeroneseEquations := function(k, n, d)
  try
    eqs := eval Sprintf("return veronese_%o_%o();", n, d);
  catch e
    printf "The equations of the %o-dimensional Veronese variety of degree %o\ 
were not computed yet. Computing them and adding them to the precomputed data.\ 
This may increase the computation time.\n", n, d;
    eqs := PrecomputeVeroneseEquations(n, d);
  end try;
  r := Rank(Parent(eqs[1]));
  ChangeUniverse(~eqs, PolynomialRing(k, r));
  return eqs;
end function;