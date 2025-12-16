forward NumberOfMonomials;
forward GetVeroneseEquations;
forward PolySubstitution;

//Generate a variety by computing the image of a Veronese variety by
//a random automorphism of the ambient projective space.
GetTwistedVeronese := function(p, n, d)
  k := GF(p);
  r := NumberOfMonomials(n, d);
  vero_eqs := GetVeroneseEquations(k, n, d);
  repeat
    T := RandomMatrix(k, r, r);
  until IsUnit(T);
  return [PolySubstitution(e, T) : e in vero_eqs];
end function;

//Checks if the projective varieties defined by sequences of equations
//are projectively equivalent under the projective transformation
//represented by T.
CheckProjectiveEquivalence := function(eqs_l, eqs_r, T)
  R := Parent(eqs_l[1]);
  I_l := ideal< R | [PolySubstitution(e, T) : e in eqs_l]>;
  I_r := ideal< R | eqs_r>;
  return I_l eq I_r;
end function;

//Generate the twist of the Lie algebra of a variety by a random matrix.
//Useful to skip the computation of the Lie algebra.
GetTwistedVeroneseRepresentation := function(p, n, d)
    k := GF(p);
    phi := VeroneseRepresentation(k, n, d);
    g := Domain(phi);
    glN := Codomain(phi);
    LieBasis := [Matrix(b @ phi) : b in Basis(g)];
    N := Degree(glN);

    repeat
      T := RandomMatrix(k, N, N);
    until IsUnit(T);

    Ti := T^-1;
    TwistedLieBasis := [T*b*Ti : b in LieBasis];
    S, inj := sub<glN | TwistedLieBasis>;
    L, psi := LieAlgebra(S);
    return L, Inverse(psi) * inj;
end function;

//p is a polynomial in n variables and M is a square matrix of order n.
//Computes the polynomial obtained from p by linear transformation of the
//variables.
PolySubstitution := function(p, M)
  R := Parent(p);
  n := Rank(R);
  return Evaluate(p, [&+[r[i]*R.i : i in [1..n]]: r in Rows(M)]);
end function;

//Computes the number of degree d homogeneous monomials with n indeterminates
NumberOfMonomials := function(n, d)
  return Binomial(n+d-1, d);
end function;

//Takes a list of homogeneous polynomials of equal degrees.
//Returns a basis of the space of polynomials spanned by elements of the list.
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
//Generates the quadratic equations for the Veronese embedding
//Not very efficient, could probably be improved.
VeroneseEquations := function(n, d)
  Z := IntegerRing();
  R := PolynomialRing(Z, n);
  mons := SetToSequence(MonomialsOfDegree(R, d));
  S := PolynomialRing(Z, #mons);
  mon_index := map< R -> { 1..#mons } | p :-> Index(mons, p)>;
  eqs := SetToSequence({
    S.((&*[R.i : i in s[1..d]]) @ mon_index) *
    S.((&*[R.i : i in s[d+1..2*d]]) @ mon_index) -
    S.((&*[R.i : i in s[1..d-1]] * R.(s[d+1])) @ mon_index) *
    S.((&*[R.i : i in s[d+2..2*d]] * R.(s[d])) @ mon_index) :
  s in Subsequences({1..n},2*d)});
  return FreeHomogeneousPolys(eqs);
end function;

//Generating the equations of Veronese embeddings is expensive with my
//implementation. This saves the equations to a magma file.
//The dollar signs need to be replaced with the letter "R".
PrecomputeVeroneseEquations := procedure(n, d)
  filename := "veronese_equations.m";
  eqs := VeroneseEquations(n, d);
  R := Universe(eqs);
  N := Rank(R);
  AssignNames(~R, [Sprintf("R.%o", i): i in [1..N]]);
  s := Sprintf("veronese_%o_%o := function()\n", n, d) cat
      Sprintf("  R := PolynomialRing(IntegerRing(), %o);\n", N) cat
      Sprintf("  return %o;\n", eqs) cat
      "  end function;\n";
  PrintFile(filename, s);
end procedure;

//Recover equations for the Veronese variety from the appropriate function.
GetVeroneseEquations := function(k, n, d)
  eqs := eval Sprintf("return veronese_%o_%o();", n, d);
  r := Rank(Parent(eqs[1]));
  ChangeUniverse(~eqs, PolynomialRing(k, r));
  return eqs;
end function;