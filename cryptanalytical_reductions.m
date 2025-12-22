/*****************************************************************
*                  Cryptanalytical Reductions                    *
*****************************************************************/

/*
  Getting twisted Veronese varieties from data related to the cryptographic
  schemes described in Section 3. Computing projective equivalences between
  varieties or to the standard Veronese variety would then break the scheme.
*/

forward VeroPublicData;

/*
  Generated public data for the scheme Vero3.
  Conjectured AES-128 parameters are a prime field of size 2^128 and d = 14.
  See Section 3.1 or the paper by Daniele Di Tullio and Manoj Gyawali :
  "A post-quantum key exchange protocol from the intersection of quadric 
  surfaces".
  Inputs:
    - k: The base field.
    - d: The degree of the Veronese embedding involved.
    - m: Size parameter for user secret keys.
  Outputs:
    Public parameters for the protocol Vero3.
*/
Vero3PublicData := function(k, d : m := 2)
  return VeroPublicData(k, d, 1, 1, m);
end function;

/*
  Generated public data for the scheme Vero2.
  See Section 3.1 for the definition.
  Inputs:
    - k: The base field.
    - d: The degree of the Veronese embedding involved.
    - m: Size parameter for user secret keys.
  Outputs:
    Public parameters for the protocol Vero3.
*/
Vero2PublicData := function(k, d : m := 3)
  return VeroPublicData(k, d, 2, 0, m);
end function;

/*
  Compute the matrix of a linear substitution operation on the space of
  monomials of degree d.
  Inputs:
    - mons: The sequence of monomials forming a basis of the space.
    - forms: The sequence of linear forms representing the substitution.
*/
PolyEvalMatrix := function(mons, forms)
  return Matrix([
      [
        MonomialCoefficient(evaluated_mon, mon_index) 
      : mon_index in mons]
      where evaluated_mon is Evaluate(mon_to_eval, forms)
    : mon_to_eval in mons]);
end function;

/*
  Generate public data for a family of cryptographic schemes relying on the
  image of some projective variety V by an "obfuscating" Veronese map 
  (which is post_composed by a secret automorphism of the ambient space).
  More precisely, the variety V is the image by the Segre embedding of
  rational normal curves of respective degrees d1 and d2.
  Inputs:
    - k: The base field of the scheme.
    - d_vero: The degree of the final obfuscating Veronese map.
    - d1, d2: The degrees of the rational normal curves defining the obfuscated
      variety.
    - m: The number of secret parameters in user's secret keys.
  Outputs:
    - Public parameters: The dimension of V, the degree of the obfuscating
      Veronese embedding and the basis of the space underlying SigmaP.
    - SigmaP: The matrix sending a random point of P1 x P1 to its image in
    the obfuscated variety (using the image of its coordimates by well
    chosen monomials)
    - M: A sequence of m Random automorphisms of the ambient space of V pushed 
    through the obfuscating Veronese map.
    
*/
VeroPublicData := function(k, d_vero, d1, d2, m)
  R4<x0, x1, y0, y1> := PolynomialRing(k, 4);
  R2 := PolynomialRing(k, 2);

  embedding := [Evaluate(m1, [x0, x1]) * Evaluate(m2, [y0, y1]):
    m1 in MonomialsOfDegree(R2, d1),
    m2 in MonomialsOfDegree(R2, d2)];
  bimons := [Evaluate(m1, [x0, x1]) * Evaluate(m2, [y0, y1]):
    m1 in MonomialsOfDegree(R2, d_vero * d1),
    m2 in MonomialsOfDegree(R2, d_vero * d2)];

  n := #embedding;
  S := PolynomialRing(k, n);
  mons := SetToSequence(MonomialsOfDegree(S, d_vero));
  N := #mons;

  T := Matrix(Random(GL(N, k)));
  Tinv := T^-1;
  SigmaPCoefs := [<Index(bimons, Evaluate(mon, embedding)), i, 1>
    : i -> mon in mons];
  SigmaP := SparseMatrix(k, #bimons, N, SigmaPCoefs) * T;

  varvec := Vector(S, [S.i : i in [1..n]]);
  M := [
    Tinv * Transpose(PolyEvalMatrix(
      mons,
      Eltseq(varvec * ChangeRing(Random(GL(n, k)), S))
    )) * T
  : _ in [1..m]];

  return <n, d_vero, bimons>, SigmaP, M;
end function;

/*
  Reconstructs the obfuscated Veronese variety from the output VeroPublicData.
  Inputs:
    - pp, SigmaP, M: See the Outputs of VeroPublicData.
  Outputs:
    - A sequence of quadratic equations defining the a twisted Veronese variety.
*/
VeroReduction := function(pp, SigmaP, M)
  n := pp[1];
  d := pp[2];
  bimons := pp[3];

  N := NumberOfColumns(SigmaP);
  k := BaseRing(SigmaP);

  quaddim := (N + 1) * N div 2 - Binomial(2 * d + n - 1, n - 1);

  R<x0, x1, y0, y1> := PolynomialRing(k, 4);
  S := PolynomialRing(k, N);
  mons := SetToSequence(MonomialsOfDegree(S, 2));

  system := ZeroMatrix(k, 0, #mons);
  i := 1;
  repeat
    points_P1_squared := [[Random(k) : i in [1..4]]: _ in [1..quaddim]];
    points_bimons := [Vector([Evaluate(bimon, a) : bimon in bimons])
      : a in points_P1_squared];
    points_vero := [Eltseq(point * SigmaP * &*[mat^Random(2) : mat in M])
      : point in points_bimons];

    system_part := Matrix([
      [Evaluate(mon, point_veronese) : mon in mons]
    : point_veronese in points_vero]);
    system := VerticalJoin(system, system_part);
  until Rank(system) + quaddim eq #mons;

  ker := NullSpace(Transpose(system));
  I := [&+[v[i] * mon : i -> mon in mons]: v in Basis(ker)];

  return I;
end function;