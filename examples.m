load "main.m";
SetSeed(123456789);
p := NextPrime(2^128);

printf "For all tests below, the base field is a prime field of size %o,", p;
print "a 128-bits prime number.";
print "We begin with computing projective equivalences to Veronese surfaces";
print "Parameters: r = 2, d = 3";
RoutineTest(p, 2, 3 : optimise_lie_computation := true);
print "========================";

print "Parameters: r = 2, d = 5";
RoutineTest(p, 2, 5 : optimise_lie_computation := true);
print "========================";

print "Parameters: r = 2, d = 8";
RoutineTest(p, 2, 8 : optimise_lie_computation := true);
print "========================";

print "We then compute equivalences to Veronese threefolds";

print "Parameters: r = 3, d = 3";
RoutineTest(p, 3, 3 : optimise_lie_computation := true);
print "========================";

print "Parameters: r = 3, d = 4";
RoutineTest(p, 3, 4 : optimise_lie_computation := true);
print "========================";

printf "In order to check computations with higher parameters, we circumvent";
printf " the bottleneck of our algorithm, which is to compute the Lie algebra";
printf " of a variety.";

printf "We compute representation isomorphism to the Lie algebra ";
printf "representation of Veronese surfaces.\n";

print "Parameters: r = 2, d = 11";
RoutineTestNoLie(p, 2, 11);
print "========================";

print "Parameters: r = 2, d = 13";
RoutineTestNoLie(p, 2, 13);
print "========================";

print "Parameters: r = 2, d = 14";
RoutineTestNoLie(p, 2, 14);
print "========================";