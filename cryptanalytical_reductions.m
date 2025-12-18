/*****************************************************************
*                  Cryptanalytical Reductions                    *
*****************************************************************/

/*
  Getting twisted Veronese varieties from data related to the cryptographic
  schemes described in Section 3. Computing projective equivalences between
  varieties or to the standard Veronese variety would then break the scheme.
*/

forward PolyEvalMatrix;

/*
  Generated public data for the scheme Vero3.
  Conjectured AES-128 parameters are a prime field of size 2^128 and d = 14.
  See Section 3.1 or the paper by Daniele Di Tullio and Manoj Gyawali :
  "A post-quantum key exchange protocol from the intersection of quadric 
  surfaces".
  Inputs:
    - Fq: The base field.
    - d: The degree of the Veronese embedding involved.
    - k: Size parameter for player's secret keys.
  Outputs:
    Public parameters for the protocol Vero3.
*/
Vero3PublicData := function(Fq, d : k := 2)
  R<x0,x1,y0,y1> := PolynomialRing(Fq, 4); // used both on P1 x P1 and on P3
  mons := SetToSequence(MonomialsOfDegree(R, d));
  bimons := [x0^i * x1^(d - i) * y0^j * y1^(d - j) : i, j in [0..d]];

  // generation of SigmaP
  n := #mons;
  T := Matrix(Random(GL(n, Fq)));
  var := [x0*y0, x1*y1, x0*y1, x1*y0];
  SigmaPCoefs := [<Index(bimons, Evaluate(mon, var)), i, 1> : i -> mon in mons];
  SigmaP := SparseMatrix(Fq, (d+1)^2, n, SigmaPCoefs) * T;

  // generation of the M_i
  Tinv := T^(-1);
  varvec := Vector(R, [x0, x1, y0, y1]);
  M := [
    Tinv * Transpose(PolyEvalMatrix(
      mons,
      Eltseq(varvec * ChangeRing(Random(GL(4, Fq)), R))
    )) * T
  : _ in [1..k]];

  return SigmaP, M;
end function;

/*
  Computes equations for a twisted veronese threefold from the data
  output by Vero3PublicData.
  Inputs:
    - SigmaP, M : Exactly the output of Vero3PublicData.
*/
Vero3Reduction := function(SigmaP, M)
  // extraction of parameters

  n := NumberOfColumns(SigmaP);
  _, d := IsSquare(NumberOfRows(SigmaP)); d -:= 1;
  Fq := BaseRing(SigmaP);
  k := #M;

  quaddim := d*(d^2-1)*(d^3 + 12*d^2 + 59*d + 66) div 72;


  // build quaddim equations

  R<x0,x1,y0,y1> := PolynomialRing(Fq, 4);

  S := PolynomialRing(Fq, n);
  mons := SetToSequence(MonomialsOfDegree(S, 2));
  bimons := [x0^i * x1^(d - i) * y0^j * y1^(d - j) : i, j in [0..d]];

  system := ZeroMatrix(Fq, 0, #mons);
  repeat
    points_P1_squared := [[Random(Fq) : i in [1..4]]: _ in [1..quaddim]];
    points_segre := [Vector([Evaluate(bimon, a) : bimon in bimons])
      : a in points_P1_squared];
    points_vero := [Eltseq(point * SigmaP * &*[M[i]^Random(2) : i in [1..k]])
      : point in points_segre];

    system_part := Matrix([
      [Evaluate(mon, point_veronese) : mon in mons]
    : point_veronese in points_vero]);
    system := VerticalJoin(system, system_part);
  until Rank(system) + quaddim eq #mons;

  ker := NullSpace(Transpose(system));
  I := [&+[v[i] * mon : i -> mon in mons]: v in Basis(ker)];

  return I;
end function;

/*
  Compute the matrix whose rows are the coefficient vectors of polynomials
  obtained from evaluating the monomials of a given dergee at a vector of
  linear forms.
  Inputs:
    - mons: The sequence of monomials, giving the order of indexation.
    - forms: The sequence of linear forms to evaluate the monomials at.
*/
PolyEvalMatrix := function(mons, forms)
  return Matrix([
      [
        MonomialCoefficient(evaluated_mon, mon_index) 
      : mon_index in mons]
      where evaluated_mon is Evaluate(mon_to_eval, forms)
    : mon_to_eval in mons]);
end function;
