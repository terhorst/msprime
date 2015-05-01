#
# Copyright (C) 2014 Jerome Kelleher <jerome.kelleher@well.ox.ac.uk>
#
# This file is part of msprime.
#
# msprime is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# msprime is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with msprime.  If not, see <http://www.gnu.org/licenses/>.
#
"""
Module responsible for identity by descent block calculations over
a tree sequence.

NOTE This module is unfinished, and highly experimental.
"""
from __future__ import division
from __future__ import print_function
from __future__ import unicode_literals

import collections
import heapq
import itertools
import json
import os
import platform
import random
import sys
import tempfile


class IdentityBlockFinder(object):
    """
    Class to find all maximal blocks of shared identity among leaf nodes.

    This class is unfinished, and highly experimental! In particular, it doesn't
    actually do anything yet.
    """
    def _get_subtrees(self, records):
        parents = {}
        times = {}
        internal_nodes = set()
        for children, parent, time in records:
            internal_nodes.add(parent)
            times[parent] = time
            for c in children:
                parents[c] = parent
        leaves = set()
        for children, parent, time in records:
            for c in children:
                if c not in internal_nodes:
                    leaves.add(c)
        subtrees = collections.defaultdict(list)
        for leaf in leaves:
            v = leaf
            while v in parents:
                v = parents[v]
            subtrees[v].append(leaf)
        l = sorted(subtrees.items(), key=lambda t: times[t[0]])
        return l

    def _check_consistency(self):
        nodes = set(self._parents.keys())
        assert len(nodes) == 2 * self._sample_size - 1
        assert nodes == set(self._leaves.keys())
        children = collections.defaultdict(set)
        for u in range(1, self._sample_size + 1):
            assert self._leaves[u] == set([u])
            v = u
            while v != 0:
                if u not in self._leaves[v]:
                    print("ERROR", u, v, self._leaves[v])
                assert u in self._leaves[v]
                w = v
                v = self._parents[v]
                children[v].add(w)
            root = w
        assert root == self._root
        stack = list(children[root])
        while len(stack) > 0:
            u = stack.pop()
            if u in children:
                leaves = set()
                for v in children[u]:
                    leaves |= self._leaves[v]
                    stack.append(v)
                if self._leaves[u] != leaves:
                    print("ERROR", u, leaves)
                assert self._leaves[u] == leaves

    def _get_mrca(self, x, y):
        """
        Returns the most recent common ancestor of nodes x and y.
        """
        x_path = [0]
        y_path = [0]
        for u, path in [(x, x_path), (y, y_path)]:
            v = u
            while v != 0:
                path.append(v)
                v = self._parents[v]
        j = -1
        while x_path[j] == y_path[j]:
            j -= 1
        return x_path[j + 1]


    def _get_mrcas(self, nodes):
        """
        Returns a map of the mrcas for all pairs of nodes in the specified
        list.
        """
        mrcas = {}
        n = len(nodes)
        for j in range(n):
            x = nodes[j]
            for k in range(j + 1, n):
                y = nodes[k]
                key = (x, y) if x < y else (y, x)
                mrcas[key] = self._get_mrca(x, y)
        return mrcas

    def __init__(self, tree_sequence):
        self._tree_sequence = tree_sequence
        self._num_loci = tree_sequence.get_num_loci()
        self._sample_size = tree_sequence.get_sample_size()
        self._parents = {}
        self._positions = {}
        self._leaves = {}
        self._root = {}

        iterator = self._tree_sequence.diffs()
        length, records_out, records_in = next(iterator)
        assert len(records_out) == 0
        for children, parent, time in records_in:
            self._positions[parent] = 0
            for j in children:
                self._parents[j] = parent
        self._root = 1
        while self._root in self._parents:
            self._root = self._parents[self._root]
        self._parents[self._root] = 0
        # propogate the leaf nodes up the tree
        for j in range(1, self._sample_size + 1):
            k = j
            while k != 0:
                if k not in self._leaves:
                    self._leaves[k] = set()
                self._leaves[k].add(j)
                k = self._parents[k]

        x = length
        for length, records_out, records_in in iterator:
            self._check_consistency()
            subtrees_out = self._get_subtrees(records_out)
            all_leaves = itertools.chain.from_iterable(
                leaves for _, leaves in subtrees_out)
            out_leaf_mrcas = self._get_mrcas(list(all_leaves))
            subtrees_in = self._get_subtrees(records_in)
            # Propogate the loss of all the subtree leaves up the tree.
            for subtree_root, subtree_leaves in subtrees_out:
                all_leaves = set()
                for subtree_leaf in subtree_leaves:
                    leaves = self._leaves[subtree_leaf]
                    all_leaves |= leaves
                    # remove any internal subtree nodes from the leaves dict.
                    v = self._parents[subtree_leaf]
                    while v != subtree_root and v in self._leaves:
                        del self._leaves[v]
                        v = self._parents[v]
                v = subtree_root
                while v != 0:
                    self._leaves[v] -= all_leaves
                    v = self._parents[v]
            # Update the overall tree structures.
            for children, parent, time in records_out:
                for j in children:
                    del self._parents[j]
            for children, parent, time in records_in:
                if parent not in self._leaves:
                    self._leaves[parent] = set()
                for j in children:
                    self._parents[j] = parent
            # Update the root, if necessary.
            v = 1
            while v in self._parents:
                v = self._parents[v]
            if v != 0:
                if self._parents[self._root] == 0:
                    del self._parents[self._root]
                    del self._leaves[self._root]
                self._root = v
                self._parents[self._root] = 0
                if self._root not in self._leaves:
                    self._leaves[self._root] = set()
            # Propogate the addition of the subtree leaves up to the root
            for root, subtree_leaves in subtrees_in:
                for subtree_leaf in subtree_leaves:
                    leaves = self._leaves[subtree_leaf]
                    v = self._parents[subtree_leaf]
                    while v != 0:
                        self._leaves[v] |= leaves
                        v = self._parents[v]
            x += length
            all_leaves = itertools.chain.from_iterable(
                leaves for _, leaves in subtrees_in)
            in_leaf_mrcas = self._get_mrcas(list(all_leaves))
            print("subtrees_out", subtrees_out)
            print("subtrees_in", subtrees_in)
            print("out_leaf_mrcas:", out_leaf_mrcas)
            print("in_leaf_mrcas:", in_leaf_mrcas)
            print()
            # TODO We need to finish this algorithm. Basically, to take things from
            # here we need to find all of the changed MRCA, and then update a
            # n * n matrix with the new position, and output all of the changed
            # haplotypes. However, there is quite a lot of sublety here, so this
            # needs to be done quite carefully.
        self._check_consistency()
