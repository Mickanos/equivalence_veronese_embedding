load "main.m";
SetSeed(123456789);
p := NextPrime(2^128);

printf "For all tests below, the base field is a prime field of size %o,", p;
print "a 128-bits prime number.";
print "We begin with computing projective equivalences to Veronese surfaces";
print "Parameters: r = 2, d = 3";
RoutineTest(p, 3, 3 : f := 0.3);

print "Parameters: r = 2, d = 5";
RoutineTest(p, 3, 5 : f := 0.2);

print "Parameters: r = 2, d = 8";
RoutineTest(p, 3, 8 : f := 0.08 , check := false);

print "We then compute equivalences to Veronese threefolds";

print "Parameters: r = 3, d = 3";
RoutineTest(p, 4, 3 : f := 0.16 , check := false);

print "Parameters: r = 3, d = 4";
RoutineTest(p, 4, 4 : f := 0.08 , check := false);

printf "In order to check computations with higher parameters, we circumvent";
printf " the bottleneck of our algorithm, which is to compute the Lie algebra";
printf " of a variety.";

printf "We compute representation isomorphism to the Lie algebra ";
printf "representation of Veronese surfaces.\n";

print "Parameters: r = 2, d = 11";
RoutineTestLie(p, 3, 11);

print "Parameters: r = 2, d = 13";
RoutineTestLie(p, 3, 13);