# Equivalence Veronese Embeddings
This repository contains an implementation for the algorithm presented in our work: *insert eprint link*.  
We implement an algorithm for computing projective equivalences between projective varieties isomorphic to Veronese varieties of various dimensions and degrees. The implementation works in any characteristic $p$, and for any dimension $n$ and degree $d$, with the exception of the case where $n = 1$ and $p \mid d + 1$ simultaneously.
## Running the code
Run magma from the root of the repository, and load either the file **main.m** or **examples.m**.
The file **examples.m** will run examples on its own, while **main.m** defines functions generating example problems and solving them: 
- **RoutineTest(q, r, d)** generates two varieties by applying random projective equivalences to the Veronese variety of dimension $n$ and degree $d$ over $\mathbb{F}_q$. It then computes a projective equivalence between the two varieties and check that the equivalence produced is correct. If the _optimise_ flag is set, the computation of the Lie algebras will be optimised (assuming that optimisation data was precomputed for the values of $n$ and $d$). This may greatly reduce the computation time.
- **RoutineTestNoLie(q, r, d)** performs the same task, except that it bypasses the computation of the Lie algebras of the varieties by directly constructing lie algebras conjugated to the Lie algebra of the Veronese variety of dimension $n$ and degree $d$ over $\mathbb{F}_q$.
- **CryptanalysisVero3**(q, d) generates public data for the scheme **Vero3** cited in our paper. It then computes the twist of the Veronese threefold of degree $d$ over the field $\mathbb{F}_q$ which underlies the security of the scheme. A projective equivalence to the Veronese threefold is then computed, thus breaking the security of the scheme for the choice of parameters. We note that while our attack has polynomial complexity, this unoptimised implementation does not break the AES-128 parameter choice for this scheme in feasible time.
## Content of the files
- **central_extension.m** implements algorithms for generating central extensions of Lie algebras using homological algebra.
- **cryptanalitical_reductions.m** implements the generation of public data for relevant cryptographic schemes and the computation of twisted Veronese varieties from these public data. As of now, only the scheme which we call**Vero3** is treated.
- **examples.m** contains code which reproduces the computations whose timings are mentioned in our paper.
- **lie_algebra_computation.m** implements the computation of the Lie algebra associated to a projective variety.
- **lie_algebra_constructions.m** implements utility functions for constructing various Lie algebras that are useful to our purposes, as well as their automorphisms.
- **lie_algebra_isomorphism.m** implements the computation of isomorphisms to the Lie algebras $\mathfrak{gl}_n$, $\mathfrak{gl}_n / k I_n$ and $\mathfrak{gl}_n / k I_n \oplus k$.
- **main.m** contains functions which run a full test of the implementation as discussed above.
- **number_equations_for_lie_algebra.m** contains code useful to the precomputation of optimisation data for the computation of the Lie algebra of twisted Veronese varieties.
- **precomputed_data** contains some precomputed data. It contains the aforementionned optimisation data, as well as equation for small parameters Veronese varieties.
- **testing_helpers.m** contains ancillary functions for generating examples such as twisted Veronese varieties, and checking that projective equivalences are correct.
- **veronese_representations_isomorphism.m** implements the computation of an isomorphism between the Lie algebra representations attached to twisted Veronese varieties. Such an isomorphism yields a projective equivalence between the varieties.