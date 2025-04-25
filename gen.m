// ********************************
// ** GENERATION OF PUBLIC DATA ***
// ********************************

//(not very fast due to polynomial arithmetic, but good enough for our purposes)

// conjectured AES-128 parameters:
// p := NextPrime(2^128);
// d := 14;

VeronesePublicData := function(Fq, d, k)
  R<x0,x1,y0,y1> := PolynomialRing(Fq, 4); // used both on P1 x P1 and on P3
  mons := SetToSequence(MonomialsOfDegree(R, d));
  bimons := [x0^i[1]*x1^(d - i[1])*y0^i[2]*y1^(d - i[2]) :
    i in CartesianPower([0..d], 2)];

  // generation of SigmaP

  n := Binomial(d + 3, 3) - 1;
  T := Random(GL(n+1, Fq));
  SigmaP := KMatrixSpace(Fq, n+1, (d+1)^2) ! 0;
  for i in [1..n+1] do
    mon := mons[i];
    bimon := Evaluate(mon, [x0*y0, x1*y1, x0*y1, x1*y0]);
    SigmaP[i][Index(bimons, bimon)] := 1;
  end for;
  SigmaP := T*SigmaP;

  // generation of the M_i

  M := [];
  Tinv := T^(-1);
  varvec := Matrix(R, 4, 1, [x0, x1, y0, y1]);
  for i in [1..k] do
    repeat
      MiP3 := Matrix(R, 4, 4, [Random(Fq) : i in [1..16]]);
    until Determinant(MiP3) ne 0;
    MiP3ev := Eltseq(MiP3*varvec);
    Mip := KMatrixSpace(Fq, n+1, n+1) ! 0;
    for r in [1..n+1] do
      evmon := Evaluate(mons[r], MiP3ev);
      evmoncoeffs := Coefficients(evmon);
      evmonmons := Monomials(evmon);
      for s in [1..#evmoncoeffs] do
        Mip[r][Index(mons, evmonmons[s])] := evmoncoeffs[s];
      end for;
    end for;
    M cat:= [T*Mip*Tinv];
  end for;

  return SigmaP, M;
end function;


// **************************************************
// ** RECONSTRUCTION OF VERONESE FROM PUBLIC DATA ***
// **************************************************


VeroneseReconstruction := function(SigmaP, M)
  // extraction of parameters

  n := NumberOfRows(SigmaP); n -:= 1;
  _, d := IsSquare(NumberOfColumns(SigmaP)); d -:= 1;
  Fq := BaseRing(SigmaP);
  k := #M;

  quaddim := d*(d^2-1)*(d^3 + 12*d^2 + 59*d + 66) div 72;


  // build quaddim equations

  R<x0,x1,y0,y1> := PolynomialRing(Fq, 4);

  S := PolynomialRing(Fq, n+1);
  mons := SetToSequence(MonomialsOfDegree(S, 2));
  nummons := Binomial(n+2, 2);

  i := 0;
  eqs := [];
  repeat
    i +:= 1;
    a := [Random(Fq) :  i in [1..4]];
    e := [Random(2) : i in [1..k]]; // maybe precompute some powers!
    point := Matrix(
      Fq,
      (d+1)^2,
      1,
      [a[1]^i[1]*a[2]^(d - i[1])*a[3]^i[2]*a[4]^(d - i[2]) :
        i in CartesianPower([0..d], 2)]
    );
    point := Eltseq(&*[M[i]^e[i] : i in [1..k]]*SigmaP*point);
    eqs cat:= [Evaluate(mon, point) : mon in mons];
    if i mod 1000 eq 0 then print i, "points sampled"; end if;
  until i ge quaddim and Rank(Matrix(Fq, i, nummons, eqs)) + quaddim eq nummons;

  bigmatrix := Matrix(Fq, i, nummons, eqs);
  ker := NullSpace(Transpose(bigmatrix));
  I := [];
  for v in Basis(ker) do
    I cat:= [&+[v[i]*mons[i] : i in [1..nummons]]];
  end for;

  return I;
end function;



// **********************************************************
// ** COMPUTE SYMMETRIC MATRIX ATTACHED TO QUADRATIC FORM ***
// **********************************************************


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

GenVeronese := function(p, d, k)
    Fq:=GF(p);
    SigmaP, M := VeronesePublicData(Fq, d, k);
    I := VeroneseReconstruction(SigmaP, M);
    return I;
end function;