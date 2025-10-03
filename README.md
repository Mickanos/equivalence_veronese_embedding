Launch magma from the the directory containing the repository.  
The file "tests.m" can be loaded to run some automatic tests.  
The file "examples.m" can be loaded to reproduce the examples discussed in
Section 7 of the paper.   
The file "Grass\_Sec.m" contains functions for computing the defining ideal of a Grassmannian of planes (i.e., projective lines) and of its secant variety, as well as for computing its Lie algebra.  
The file "Lie\_Defect.m" describes the experiment for Remark 6.3 for Veronese varieties.  
The file "gen.m" contains, amongst other things, code related to the security reduction discussed in Section 4 of the paper for the schemes **vero2** and **vero3**.  
Otherwise, simply load "main.m". The procedure `RoutineTest` generates a random
variety equivalent to a Veronese variety, forgets the equivalence and computes
it again. The procedure RoutineTestLie does the same, but skips the computation
of the Lie algebra, which is the bottleneck.
