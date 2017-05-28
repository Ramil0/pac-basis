""" Module for computing a PAC-basis.

This module allows computing implication bases based on queries to
oracles. Efficient methods to compute implication bases are unknown in
general, and standard algorithms may thus be too slow. To tackle this
problem, we can compute bases that are approximately correct with high
probability. For the given formal context K the basis H is called
probably approximately correct (PAC-basis) with accuracy epsilon > 0 and
confidence delta > 0 if Pr(horn_distance(H, K) > epsilon) < delta [1].

For more details about the PAC algorithm used in this module, see [1].

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

"""

from __future__ import print_function

import math
import random
import itertools
from time import time

# Local changes:
#   Added __hash__ method to fca.implication.Implication.
#   Changed ___repr__ and __cmp__ methods.
from fca.implication import Implication
from fca.context import Context
from fca.algorithms.nextclosure import next_closure, all_closures   
from fca.algorithms.closure_operators import aclosure, lin_closure


def _closed(attribute_subset, implications_set):
    """ Checks whether the given subset of attributes is closed under the set
        of implications.

        The function is used by MembershipEquivalenceExpert and Learner
        classes.

        Args:
            attribute_subset: An object represented as a subset of attributes.
            implications_set: Set of implications.

        Returns:
            True if attribute_subset is closed under the given set of
            implications and False otherwise.

    """
    for implication in implications_set:
        if not implication.is_respected(attribute_subset):
            return False
    return True


def horn_distance(implications_set, context):
    context_closure = lambda attributes_subset: aclosure(attributes_subset, 
                                                         context)
    implications_set_closure = lambda attributes_subset: sorted(
        lin_closure(set(attributes_subset), implications_set))
    context_intents = set([",".join(sorted(attributes_subset)) 
        for attributes_subset in all_closures(context.attributes, 
                                              context_closure)])
    implications_set_intents = set([",".join(sorted(attributes_subset)) 
        for attributes_subset in all_closures(context.attributes, 
                                              implications_set_closure)])
    return len(context_intents.symmetric_difference(
        implications_set_intents)) / (2.0 ** len(context.attributes))


class ImplicationExpert(object):
    """ Answers to two types of queries:
            is_valid,
            request of counterexample.
    """
    def __init__(self, formal_context):
        """ Args:
                formal_context: An object of type fca.Context representing a
                                formal context to work with.
        """
        self.formal_context = formal_context
        self.implication_query_count = 0

    def is_valid(self, implication):
        """ Checks whether the given implication is valid in the formal
            context.
        """
        return self.provide_counterexample(implication) is None

    def provide_counterexample(self, implication):
        """ Provides a counterexample if the implication is not valid in the
            formal context.

            Args:
                implication: An implication to check.

            Returns:
                The first object from the context that violates the given
                implication and None if all objects are closed under it.
        """
        self.implication_query_count += 1
        for obj in self.formal_context.intents():
            if not implication.is_respected(obj):
                return obj
        return None


def _select_random_uniform_subset(attributes):
    """ Select a random subset of attributes uniformly over all possible
        subsets.
    """
    random_subset = set()
    for attribute in attributes:
        if random.getrandbits(1):
            random_subset.add(attribute)
    return random_subset


class MembershipEquivalenceExpert(object):
    """ Answers to two types of queries:
            is_member (membership query),
            is_approximately_equivalent (approximate equivalence query),
            is_equivalent (equivalence query).
    """

    def __init__(self, attributes, implication_expert, mode='pow2', 
                 degree=1):
        """ Args:
                attributes: A set of attributes.
                implication_expert: ImplicationExpert object initialized with
                                    a formal context.
        """
        self.implication_expert = implication_expert
        self.attributes = attributes
        self.mode = mode
        self.degree = degree
        self.membership_query_count = 0
        self.approximately_equivalence_query_count = 0

    def is_member(self, attribute_subset):
        """ Checks whether the given subset of attributes is a model of actual
            implication basis.

            Args:
                attribute_subset: An object represented as a subset of
                                  attributes.

            Returns:
                True if the given subset of attributes is a model of
                actual implication basis and False otherwise.
        """
        self.membership_query_count += 1
        implication = Implication(attribute_subset, set())
        for attribute in self.attributes:
            if attribute not in attribute_subset:
                implication = Implication(attribute_subset, {attribute})
                if self.implication_expert.is_valid(implication):
                    return False
        return True

    def is_approximately_equivalent(self, hypothetical_basis, epsilon, delta):
        """ Checks whether the given basis is equivalent to the actual
            one with accuracy epsilon and confidence delta.

            This function tries to find a counterexample for hypothetical basis
            by checking random subsets of attributes generated at random
            uniformly.

            Args:
                hypothetical_basis: A basis to check.
                epsilon: The number from (0, 1) indicating the accuracy.
                delta: The number from (0, 1) indicating the confidence level.

            Returns:
                A counterexample if found, None otherwise.
        """
        self.approximately_equivalence_query_count  += 1    
        n = self.approximately_equivalence_query_count
        q = self.degree
        if self.mode == 'telescoping':
            num_attempts = math.log(
                n ** q * (n + 1) ** q / 
                (delta * ((n + 1) ** q - n ** q))) / epsilon
        elif self.mode == 'pow2':
            num_attempts = (self.approximately_equivalence_query_count - 
                            math.log(delta)) / epsilon

        num_attempts = int(math.ceil(num_attempts))
        for _ in xrange(num_attempts):
            random_subset = _select_random_uniform_subset(self.attributes)
            if _closed(random_subset, hypothetical_basis) ^ self.is_member(
                    random_subset):
                return random_subset
        return None

    def is_strongly_approximately_equivalent(self, hypothetical_basis, epsilon,
                                             delta):
        """ Checks whether the given basis is equivalent to the actual
            one with accuracy epsilon and confidence delta.

            This function tries to find a counterexample for hypothetical basis
            by checking random subsets of attributes generated at random
            uniformly.

            Args:
                hypothetical_basis: A basis to check.
                epsilon: The number from (0, 1) indicating the accuracy.
                delta: The number from (0, 1) indicating the confidence level.

            Returns:
                A counterexample if found, None otherwise.
        """
        self.approximately_equivalence_query_count  += 1    
        n = self.approximately_equivalence_query_count
        q = self.degree
        if self.mode == 'telescoping':
            num_attempts = math.log(
                n ** q * (n + 1) ** q / 
                (delta * ((n + 1) ** q - n ** q))) / epsilon
        elif self.mode == 'pow2':
            num_attempts = (self.approximately_equivalence_query_count - 
                            math.log(delta)) / epsilon

        num_attempts = int(math.ceil(num_attempts))
        for _ in xrange(num_attempts):
            random_subset = _select_random_uniform_subset(self.attributes)
            closed_random_subset = lin_closure(random_subset, 
                hypothetical_basis)
            implication = Implication(random_subset, closed_random_subset)
            counterexample = self.implication_expert.provide_counterexample(
                    implication)
            if counterexample:
                return counterexample
            if not self.is_member(closed_random_subset):
                return closed_random_subset
        return None

    def is_equivalent(self, hypothetical_basis):
        """ Checks whether the given basis is equivalent to the actual.

            This function tries to find a counterexample for hypothetical basis
            by checking all possible subsets of attributes.

            Args:
                hypothetical_basis: A basis to check.

            Returns:
                A counterexample if found, None otherwise.
        """
        for subset_size in xrange(len(self.attributes) + 1):
            for subset in itertools.combinations(self.attributes, subset_size):
                subset = set(subset)
                if _closed(subset, hypothetical_basis) ^ self.is_member(
                        subset):
                    return subset
        return None

    def set_counts_to_zero(self):
        self.implication_expert.implication_query_count = 0
        self.membership_query_count = 0
        self.approximately_equivalence_query_count = 0

    def query_statistics(self):
        return {'implication queries': 
                    self.implication_expert.implication_query_count,
                'is_member queries': self.membership_query_count, 
                'is_approximately_equivalent queries': 
                    self.approximately_equivalence_query_count}


def _cleanup(learn_function):
    """ A wrapper for Learner.learn method.
    """
    def wrapped(self, *args, **kwargs):
        """ Set MembershipEquivalenceExpert.count to zero and prints
            whether or not learning was successful depending on the status
            returned.
        """
        result = learn_function(self, *args, **kwargs)
        self.running_time = time() - self.running_time
        self.learning_statistics = self.expert.query_statistics()
        self.learning_statistics['running time'] = self.running_time
        self.expert.set_counts_to_zero()
        if result == 0:
            self._log_info("\nPAC-basis is successfully found.")
        else:
            self._log_info('Number of iterations is exceeded.')
        return result
    return wrapped


class Learner(object):
    """ Interacts with a membership and equivalence oracles to find a PAC-basis
        for the hidden context.
    """
    def __init__(self, attributes, expert, epsilon, delta, mode=None):
        """ Args:
                attributes: A set of attributes.
                expert: An expert to interact with.
                epsilon: The number from (0, 1) indicating the accuracy.
                delta: The number from (0, 1) indicating the confidence level.
        """
        self.attributes = attributes
        self.expert = expert
        self.epsilon = epsilon
        self.delta = delta
        self.mode = mode
        self.pac_basis = []
        self._verbose_learning = False
        self.running_time = 0.0
        self.learning_statistics = {}

    def _log_info(self, *args, **kwargs):
        """ For printing logs when verbose is enabled.
        """
        if self._verbose_learning:
            print(*args, **kwargs)

    def query_equivalence_counterexample(self):
        if self.mode == 'strong':
            return self.expert.is_strongly_approximately_equivalent(
                    self.pac_basis, self.epsilon, self.delta)
        else:
            return self.expert.is_approximately_equivalent(
                    self.pac_basis, self.epsilon, self.delta)

    @_cleanup
    def learn(self, max_iterations=None, verbose=False):
        """ Computes PAC-basis by interacting with MembershipEquivalenceExpert.

            Args:
                max_iterations: The maximum number of iterations for correction
                                of the hypothetical basis. If None, then the
                                number of iterations is not limited.
                verbose (default=False): Enable verbose output.
        """
        self._verbose_learning = verbose
        self.running_time = time()
        self.pac_basis = []
        while True:
            self._log_info('%d. Hypothetical basis:' % 
                (self.expert.approximately_equivalence_query_count + 1),
                 self.pac_basis)
            counterexample = self.query_equivalence_counterexample()
            if counterexample is None:
                return 0
            if _closed(counterexample, self.pac_basis):
                # Negative counterexample.
                self._log_info('Negative counterexample:',
                               list(counterexample), end='\n\n')
                found = False
                for implication in self.pac_basis:
                    premise = implication.premise
                    new_premise = premise & counterexample
                    if new_premise < premise and not self.expert.is_member(
                            new_premise):
                        implication.set_premise(new_premise)
                        found = True
                        break
                if not found:
                    self.pac_basis.append(
                        Implication(counterexample, set(self.attributes)))
            else:
                # Positive counterexample.
                self._log_info('Positive counterexample:',
                               list(counterexample), end='\n\n')
                for implication in self.pac_basis:
                    if not implication.is_respected(counterexample):
                        implication.set_conclusion(implication.conclusion &
                                                   counterexample)
            if (max_iterations and 
                self.expert.approximately_equivalence_query_count > 
                    max_iterations):
                return 1

    def get_basis(self):
        """ Returns a PAC-basis computed.
        """
        return self.pac_basis

    def get_statistics(self):
        return self.learning_statistics


def _get_mask(attributes_subset, attributes):
    mask = []
    for attribute in attributes:
        if attribute in attributes_subset:
            mask.append(True)
        else:
            mask.append(False)
    return mask


class AttributeExplorer(object):
    def __init__(self, attributes, implication_expert, 
                 initial_context=None):
        self.attributes = attributes
        self.implication_expert = implication_expert
        self.basis = []
        if initial_context is None:
            self.context = Context([], [], attributes)
        else:
            self.context = initial_context
        self.running_time = 0.0
        self.learning_statistics = {}
    
    def learn(self):
        self.running_time = time()
        current_attributes = []
        while len(current_attributes) < len(self.attributes):
            while True:
                current_closure = aclosure(current_attributes, self.context)
                if current_attributes == current_closure:
                    break
                implication = Implication(set(current_attributes), 
                                          set(current_closure))
                counterexample = (
                    self.implication_expert.provide_counterexample(
                        implication))
                if counterexample is None:
                    self.basis.append(implication)
                    break
                else:
                    self.context.add_object(_get_mask(sorted(counterexample),
                                                      self.attributes),
                                            self.context.get_size()[0])
            attributes_closure = lambda attributes_subset: sorted(
                lin_closure(set(attributes_subset), self.basis))
            current_attributes = next_closure(current_attributes, 
                                              self.attributes, 
                                              attributes_closure)
        self.running_time = time() - self.running_time
        self.learning_statistics['running time'] = self.running_time
        self.learning_statistics['implication queries'] = (
            self.implication_expert.implication_query_count)
        self.implication_expert.implication_query_count = 0
            
    def get_basis(self):
        return self.basis
    
    def get_context(self):
        return self.context
    
    def get_statistics(self):
        return self.learning_statistics
