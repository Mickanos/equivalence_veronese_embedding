load "main.m";

no_sol := 0;
p := NextPrime(2^20);
F := GF(p);
k := 2;
n := 4;
d := 2;
for _ in [1..50] do
    //Generates quadratic equations for a variety projectively equivalent to
    //the veronese 3-fold of degree 2.
    eqs := GenToyVeronese(p, d, k);
    //Tries to compute a projective equivalence
    sol := EquivalenceToVeronese(n, d, eqs);
    if IsEmpty(sol) then
        no_sol +:= 1;
    else
        T := sol[1];
        assert CheckEquivalenceToVeronese(eqs, T, n, d);
    end if;
end for;
print "The proportion of tests where no solution was found is ", no_sol/50;