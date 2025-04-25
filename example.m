load "main.m";

no_sol := 0;
k := GF(NextPrime(2^20));
n := 4;
d := 2;
for _ in [1..50] do
    //Generates quadratic equations for a variety projectively equivalent to
    //the veronese 3-fold of degree 2.
    eqs := GenToyVeronese();
    //Tries to compute a projective equivalence
    sol := EquivalenceToVeronese(n, d, eqs);
    if IsEmpty(sol) then
        no_sol +:= 1;
    else
        T := sol[1];
        //We check that the matrix T gives a projective equivalence
        //with the Veronese embedding. 
        vero_eqs := VeroneseEquations(k, n, d);
        R := Parent(eqs[1]);
        I := ideal<R | vero_eqs>;
        assert ideal<R | [PolySubstitution(e, T) : e in eqs]> eq I;
    end if;
end for;
print "The proportion of tests where no solution was found is ", no_sol/50;