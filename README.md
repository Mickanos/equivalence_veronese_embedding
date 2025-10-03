Launch magma from the the directory containing the repository.  
The file "tests.m" can be loaded to run some automatic tests.  
The file "examples.m" can be loaded to reproduce the examples discussed in
Section 7 of the paper. 
Otherwise, simply load "main.m". The procedure `RoutineTest` generates a random
variety equivalent to a Veronese variety, forgets the equivalence and computes
it again. The procedure RoutineTestLie does the same, but skips the computation
of the Lie algebra, which is the bottleneck.
