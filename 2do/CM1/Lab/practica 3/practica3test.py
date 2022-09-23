#! /usr/bin/python
# -*- coding: utf-8 -*-

import unittest

from practica3 import (esCaminoEuleriano,
                              esCicloEuleriano,
                              esCaminoHamiltoniano,
                              esCicloHamiltoniano,
                              tieneCaminoEuleriano)


class TestIsHamiltoneanTrail(unittest.TestCase):
    graph_1 = ([], [])
    graph_2 = (['a'], [])
    graph_3 = (['a'], [('a', 'a')])
    graph_4 = (['a', 'b'], [('a', 'b')])
    graph_5 = (['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])
    graph_6 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('a', 'd'), ('c', 'd'), ('d', 'a')])

    is_trail_cases = [
        (graph_1, []),
        (graph_4, [('a', 'b')]),
        (graph_5, [('a', 'b'), ('b', 'c')]),
        (graph_6, [('a', 'b'), ('b', 'c'), ('c', 'd')])
    ]

    is_not_trail_cases = [
        (graph_1, [('a', 'b')]),
        (graph_2, [('b', 'a')]),
        (graph_2, []),
        (graph_3, [('b', 'a')]),
        (graph_3, []),
        (graph_4, []),
        (graph_4, [('b', 'a')]),
        (graph_4, [('a', 'c'), ('c', 'b')]),
        (graph_5, [('b', 'c'), ('a', 'b')]),
        (graph_6, [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'd')])
    ]

    def test_is_trail_cases(self):
        for graph, path in self.is_trail_cases:
            result = esCaminoHamiltoniano(graph, path)
            self.assertTrue(
                result,
                'caso: esCaminoHamiltoniano({}, {})'.format(graph, path)
            )

    def test_is_not_trail_cases(self):
        for graph, path in self.is_not_trail_cases:
            result = esCaminoHamiltoniano(graph, path)
            self.assertFalse(
                result,
                'caso: esCaminoHamiltoniano({}, {})'.format(graph, path)
            )


class TestIsHamiltoneanCircuit(unittest.TestCase):
    graph_1 = ([], [])
    graph_2 = (['a'], [])
    graph_3 = (['a'], [('a', 'a')])
    graph_4 = (['a', 'b'], [('a', 'b'), ('b', 'a')])
    graph_5 = (['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])
    graph_6 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('a', 'd'), ('c', 'd'), ('d', 'a')])
    graph_7 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'b')])
    graph_8 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('c', 'a'), ('a', 'd')])

    is_circuit_cases = [
        (graph_1, []),
        (graph_3, [('a', 'a')]),
        (graph_4, [('a', 'b'), ('b', 'a')]),
        (graph_6, [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'a')])
    ]

    is_not_circuit_cases = [
        (graph_1, [('a', 'b')]),
        (graph_2, [('b', 'a')]),
        (graph_2, []),
        (graph_3, [('b', 'a')]),
        (graph_3, []),
        (graph_4, []),
        (graph_4, [('a', 'c'), ('c', 'a')]),
        (graph_5, [('b', 'c'), ('a', 'b')]),
        (graph_6, [('a', 'b'), ('b', 'c'), ('c', 'd')]),
        (graph_7, [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'b')]),
        (graph_8, [('a', 'b'), ('b', 'c'), ('c', 'a'), ('a', 'd')])
    ]

    def test_is_circuit_cases(self):
        for graph, path in self.is_circuit_cases:
            result = esCicloHamiltoniano(graph, path)
            self.assertTrue(
                result,
                'caso: esCicloHamiltoniano({}, {})'.format(graph, path)
            )

    def test_is_not_circuit_cases(self):
        for graph, path in self.is_not_circuit_cases:
            result = esCicloHamiltoniano(graph, path)
            self.assertFalse(
                result,
                'caso: esCicloHamiltoniano({}, {})'.format(graph, path)
            )


class TestIsEulerianTrail(unittest.TestCase):
    graph_1 = ([], [])
    graph_2 = (['a'], [])
    graph_3 = (['a'], [('a', 'a')])
    graph_4 = (['a', 'b'], [('a', 'b')])
    graph_5 = (['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])
    graph_6 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('a', 'd'), ('c', 'd'), ('d', 'a')])

    is_trail_cases = [
        (graph_1, []),
        (graph_2, []),
        (graph_4, [('a', 'b')]),
        (graph_5, [('a', 'b'), ('b', 'c')]),
        (graph_6, [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'a'), ('a', 'd')])
    ]

    is_not_trail_cases = [
        (graph_1, [('a', 'b')]),
        (graph_2, [('b', 'a')]),
        (graph_3, [('b', 'a')]),
        (graph_3, []),
        (graph_4, []),
        (graph_4, [('b', 'a')]),
        (graph_4, [('a', 'c'), ('c', 'b')]),
        (graph_5, [('b', 'c'), ('a', 'b')]),
        (graph_6, [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'd')])
    ]

    def test_is_trail_cases(self):
        for graph, path in self.is_trail_cases:
            result = esCaminoEuleriano(graph, path)
            self.assertTrue(
                result,
                'caso: esCaminoEuleriano({}, {})'.format(graph, path)
            )

    def test_is_not_trail_cases(self):
        for graph, path in self.is_not_trail_cases:
            result = esCaminoEuleriano(graph, path)
            self.assertFalse(
                result,
                'caso: esCaminoEuleriano({}, {})'.format(graph, path)
            )


class TestIsEulerianCircuit(unittest.TestCase):
    graph_1 = ([], [])
    graph_2 = (['a'], [])
    graph_3 = (['a'], [('a', 'a')])
    graph_4 = (['a', 'b'], [('a', 'b')])
    graph_5 = (['a', 'b', 'c'], [('a', 'b'), ('b', 'c')])
    graph_6 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('a', 'd'), ('c', 'd'), ('d', 'a')])
    graph_7 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'a')])

    is_trail_cases = [
        (graph_1, []),
        (graph_2, []),
        (graph_7, [('b', 'c'), ('c', 'd'), ('d', 'a'), ('a', 'b')])
    ]

    is_not_trail_cases = [
        (graph_1, [('a', 'b')]),
        (graph_2, [('b', 'a')]),
        (graph_3, [('b', 'a')]),
        (graph_3, []),
        (graph_4, []),
        (graph_4, [('b', 'a')]),
        (graph_4, [('a', 'c'), ('c', 'b')]),
        (graph_5, [('b', 'c'), ('a', 'b')]),
        (graph_6, [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'd')]),
        (graph_5, [('a', 'b'), ('b', 'c')]),
        (graph_6, [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'a'), ('a', 'd')])
    ]

    def test_is_trail_cases(self):
        for graph, path in self.is_trail_cases:
            result = esCicloEuleriano(graph, path)
            self.assertTrue(
                result,
                'caso: esCicloEuleriano({}, {})'.format(graph, path)
            )

    def test_is_not_trail_cases(self):
        for graph, path in self.is_not_trail_cases:
            result = esCicloEuleriano(graph, path)
            self.assertFalse(
                result,
                'caso: esCicloEuleriano({}, {})'.format(graph, path)
            )


class TestHasEulerianTrail(unittest.TestCase):
    graph_1 = ([], [])
    graph_2 = (['a'], [])
    graph_3 = (['a'], [('a', 'a')])
    graph_4 = (['A', 'B', 'C', 'D'], [('A', 'C'), ('A', 'D'), ('B', 'C'), ('B', 'D'), ('C', 'D')])
    graph_5 = (['A', 'B', 'C', 'D'], [('A', 'C'), ('A', 'D'), ('B', 'C'), ('B', 'D')])
    graph_6 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('a', 'd'), ('c', 'd')])
    graph_7 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('c', 'd'), ('d', 'b')])
    graph_8 = (['a', 'b', 'c', 'd'],
               [('a', 'b'), ('b', 'c'), ('c', 'a'), ('a', 'd')])
    graph_9 = (['A', 'B', 'C', 'D'], [('A', 'B'), ('A', 'C'), ('A', 'D'), ('B', 'C'), ('B', 'D'), ('C', 'D')])
    graph_10 = (['A', 'B', 'C', 'D', 'E', 'F'],
                [('A', 'B'), ('A', 'C'), ('A', 'D'), ('B', 'C'), ('B', 'D'), ('C', 'D'), ('B', 'E'), ('C', 'E'),
                 ('E', 'F')])
    graph_11 = (['A', 'B', 'C', 'D'], [('A', 'B'), ('A', 'C'), ('A', 'D')])

    has_trail_cases = [
        graph_1,
        graph_2,
        graph_4,
        graph_5,
        graph_6,
        graph_7,
        graph_8
    ]

    has_not_trail_cases = [
        graph_9,
        graph_10,
        graph_11
    ]

    def test_has_trail_cases(self):
        for graph in self.has_trail_cases:
            result = tieneCaminoEuleriano(graph)
            self.assertTrue(
                result,
                'caso: tieneCaminoEuleriano({})'.format(graph)
            )

    def test_has_not_trail_cases(self):
        for graph in self.has_not_trail_cases:
            result = tieneCaminoEuleriano(graph)
            self.assertFalse(
                result,
                'caso: tieneCaminoEuleriano({})'.format(graph)
            )

class TestFindEulerianCircuit(unittest.TestCase):
    pass


if __name__ == '__main__':
    unittest.main()