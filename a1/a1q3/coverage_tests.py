import unittest

from . import token_with_escape 


class CoverageTests(unittest.TestCase):
    def test_1(self):
        """Node Coverage but not Edge Coverage"""
        # YOUR CODE HERE
        # TRNC = {{8,9,10Con1}, 10Cond2, 11, 13, 14, 15, 16, 17, 18, 19, 21, 23, 24, 26}
        # Edges not covered = {({8,9,10Con1},13), ({10Con2,13})}
        # I have excluded the (23,14) edge as it is infeasible.
        result = token_with_escape('|abc^^^^|||def')
        self.assertEqual(result,['', 'abc^^', '', '', 'def'])
        

    def test_2(self):
        """Edge Coverage but not Edge Pair Coverage"""
        # YOUR CODE HERE
        # Does not cover [13,14,26] edge-pair. Can be covered only if the input is "".

        result = token_with_escape('|')
        self.assertEqual(result,['',''])

        result = token_with_escape('a')
        self.assertEqual(result,['a'])

        result = token_with_escape('^a')
        self.assertEqual(result,['a'])

        
        result = token_with_escape("|b")
        self.assertEqual(result,['','b'])

        result = token_with_escape("||")
        self.assertEqual(result,['','',''])

        result = token_with_escape("a|b")
        self.assertEqual(result,['a','b'])

        
        result = token_with_escape("a^^|b")
        self.assertEqual(result,['a^','b'])
        

    def test_3(self):
        """Edge Pair Coverage but not Prime Path Coverage"""
        # YOUR CODE HERE
        # Does not cover the prime path: 14,15,16,18,19,14
        # The above mentioned prime path can only be covered if there are two consecutive seperators. That is, if the input would be "a||b"

        result = token_with_escape("a|")
        self.assertEqual(result, ["a", ""])

        result = token_with_escape("")
        self.assertEqual(result,[""])

        result = token_with_escape("a^")
        self.assertEqual(result,["a"])

        result = token_with_escape("|")
        self.assertEqual(result,["",''])

        result = token_with_escape("a^bc")
        self.assertEqual(result,["abc"])

        result = token_with_escape('b|^a')
        self.assertEqual(result,["b","a"])

