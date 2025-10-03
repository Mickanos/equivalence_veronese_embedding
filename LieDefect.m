// Code for running the experiment reported in Remark 6.3 for the Veronese case

// characteristic
p := 3;

// number of variables (i.e., we are embedding P^(num_vars - 1))
num_vars := 3;

// number of retries
num_tries := 5;

// upleness of embedding
range_of_ds := [2..30];

// =============================================================

print "Computing rank defects for", num_vars, "variables in char", p;

for d in range_of_ds do

  Fp := GF(p);
  R := PolynomialRing(Fp, num_vars);
  mons := SetToSequence(MonomialsOfDegree(R, d));
  n := #mons;

  // build matrices D

  mat_sp := KMatrixSpace(Fp, n, n);
  D := [];
  for i in [1..num_vars] do
    for j in [1..num_vars] do
      mat := mat_sp ! 0;
  	  for k in [1..n] do
        image_term := R.i*Derivative(mons[k], j);
	    if image_term ne 0 then
	      lc := LeadingCoefficient(image_term);
		  image_mon := image_term/lc;
		  mat[Index(mons, image_mon)][k] := lc;
	    end if;
      end for;
	  D cat:= [mat];
    end for;
  end for;

  // build num_tries matrices T and list rank defects

  expected_rank := n^2 - 1;
  // R_for_T := PolynomialRing(Fp, n^2);
  // Tvar := Matrix(R_for_T, n, n, [R_for_T.i : i in [1..n^2]]);

  defects := [];
  for i in [1..num_tries] do
    system := ZeroMatrix(Fp, num_vars^2*n^2, n^2);
    repeat
      T := Random(KMatrixSpace(Fp, n, n));
    until Determinant(T) ne 0;
    Tinv := T^(-1);
    B := [Tinv*Dmat*T : Dmat in D];
	row_index := 0;
    for j in [1..num_vars^2] do
	  for k in [1..n] do
	    for l in [1..n] do
          row_index +:= 1;
          // entry (k,l) is sum_s T_ks*Bsl - sum_s D_ks*Tsl = sum_s (Bsl*Tks - Dks*Tsl)
          for s in [1..n] do
            system[row_index][(k-1)*n + s] +:= B[j][s][l];
            system[row_index][(s-1)*n + l] -:= D[j][k][s];			
          end for;		  
		end for;
	  end for;
      // eqns cat:= Eltseq(Tvar*(Parent(Tvar) ! B[j]) - (Parent(Tvar) ! D[j])*Tvar);
    end for;
    defects cat:= [expected_rank - Rank(system)];
  end for;

  print d, defects;

end for;