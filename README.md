This is a module for computing PAC bases.

This module allows computing implication bases based on queries to
oracles. Efficient methods to compute implication bases are unknown in
general, and standard algorithms may thus be too slow. To tackle this
problem, we can compute bases that are approximately correct with high
probability. For the given formal context K the basis H is called
probably approximately correct (PAC-basis) with accuracy epsilon > 0 and
confidence delta > 0 if Pr(horn_distance(H, K) > epsilon) < delta [1].

For more details about the algorithm used in this module, see [1].

Example of usage:

>>> from fca.context import Context
>>> from pac_basis import *
>>> binary_relation = [[ True, False, False,  True],
...                    [ True, False,  True, False],
...                    [False,  True,  True, False],
...                    [False,  True,  True,  True]]
>>> attributes = ['a', 'b', 'c', 'd']
>>> formal_context = Context(binary_relation, range(4), attributes)
>>> implication_expert = ImplicationExpert(formal_context)
>>> membership_equivalence_expert = MembershipEquivalenceExpert(attributes,
...                                                     implication_expert)
>>> learner = Learner(attributes, membership_equivalence_expert,
...                   epsilon=0.01, delta=0.1)
>>> status = learner.learn(max_iterations=1000)
>>> if status == 0:
...     pac_basis = learner.get_basis()
>>> else:
...     print('Number of iterations is exceeded')


[1] Borchmann, D., Hanika, T., Obiedkov, S.: On the Usability of 
Probably Approximately Correct Implication Bases - arXiv preprint 
arXiv:1701.00877, 2017.
