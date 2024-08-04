import unittest

from . import ast, undef_visitor


class TestUndefVisitor(unittest.TestCase):
    def test1(self):
        prg1 = "x := 10; y := x + z"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        # UNCOMMENT to run the test
        self.assertEqual (set ([ast.IntVar('z')]), uv.get_undefs ())

    def testAssume(self):
        prg1 = "assume x > 0"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        # UNCOMMENT to run the test
        self.assertEqual (set ([ast.IntVar('x')]), uv.get_undefs ())

    def testAssert(self):
        prg1 = "assert x > 0"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        # UNCOMMENT to run the test
        self.assertEqual (set ([ast.IntVar('x')]), uv.get_undefs ())

    def testHavoc(self):
        prg1 = "havoc x; if x > 5 then y := x + 1 else z := 8; x := z +1"
        ast2 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast2)
        self.assertEqual(set ([ast.IntVar('z')]), uv.get_undefs ())

    def testWhile(self):
        prg1 = "x := 2; while y > 0 do {z := x + 3; skip}; y := z - 1"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        # UNCOMMENT to run the test
        self.assertEqual (set ([ast.IntVar('y'), ast.IntVar('z')]), uv.get_undefs ())

    def testIf(self):
        prg1 = "x := 5; if x < 0 then y := 5 else z := 5; z := x + y + z"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        # UNCOMMENT to run the test
        self.assertEqual (set ([ast.IntVar('y'), ast.IntVar('z')]), uv.get_undefs ())

    def testIfTwo(self):
        prg1 = "if true then y := y + 2; if false then skip else {x := 5; z := z + 5}"
        ast1 = ast.parse_string(prg1)
        print (ast1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEqual(set([ast.IntVar('y'),ast.IntVar('z')]), uv.get_undefs())

    def test_bexp(self):
        prg1 = "a := b - c"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEqual(set([ast.IntVar('b'), ast.IntVar('c')]), uv.get_undefs())