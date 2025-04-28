load "utility.m";
load "gen.m";
load "lie_algebra_isomorphism.m";
load "projective_equivalence.m";

RoutineTest := procedure(p, d)
    n := 4;
    k := 2;
    print "Time to generate equations:";
    time eqs := GenVeronese(p, d, k);
    print "Time to look for a projective equivalence:";
    time sol := EquivalenceToVeronese(n, d, eqs);
    if IsEmpty(sol) then
        print "The isomorphism of Lie algebras did not yield a projective",  
        " equivalence.";
    else
        if CheckEquivalenceToVeronese(eqs, sol[1], n, d) then
            print "An equivalence was found.";
        else
            print "The program did output an incorrect solution.";
        end if;
    end if;
end procedure;