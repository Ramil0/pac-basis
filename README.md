This is a module for computing PAC bases.

This module allows computing implication bases based on queries to
oracles. Efficient methods to compute implication bases are unknown in
general, and standard algorithms may thus be too slow. To tackle this
problem, we can compute bases that are approximately correct with high
probability. For the given formal context K the basis H is called
probably approximately correct (PAC-basis) with accuracy epsilon > 0 and
confidence delta > 0 if Pr(horn_distance(H, K) > epsilon) < delta [1].

For more details about the algorithm used in this module, see [1].

[1] Borchmann, D., Hanika, T., Obiedkov, S.: On the Usability of 
Probably Approximately Correct Implication Bases - arXiv preprint 
arXiv:1701.00877, 2017.
