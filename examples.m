load "main.m";
SetSeed(123456789);
p := NextPrime(2^128);

printf "For all tests below, the base field is a prime field of size %o, \
a 128-bits prime number.\nWe begin with computing public parameters for \
the scheme Vero2, recovering the obfuscated Veronese variety and then \ computing a projective equivalence to the standard Veronese variety.", p;
print "Parameter: d = 3";
CryptanalysisVero2(p, 3);
print "========================";

print "Parameter: d = 5";
CryptanalysisVero2(p, 5);
print "========================";

print "Parameter: d = 8";
CryptanalysisVero2(p, 8);
print "========================";

print "We then do the same for Vero3.";

print "Parameters: r = 3, d = 3";
CryptanalysisVero3(p, 3);
print "========================";

print "Parameters: r = 3, d = 4";
CryptanalysisVero3(p, 4);
print "========================";

print "In order to check computations with higher parameters, we circumvent\
the bottleneck of our algorithm, which is to compute the Lie algebra\
of a variety.\nWe compute representation isomorphism to the Lie algebra \
representation of Veronese surfaces.";

print "Parameters: r = 2, d = 11";
RoutineTestNoLie(p, 2, 11);
print "========================";

print "Parameters: r = 2, d = 13";
RoutineTestNoLie(p, 2, 13);
print "========================";

print "Parameters: r = 2, d = 14";
RoutineTestNoLie(p, 2, 14);
print "========================";