# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import unittest

from . import ast, int, mockVisitor


class TestInt(unittest.TestCase):
    def test_one(self):
        prg1 = "x := 10; print_state"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn("x", st.env)
        # x is 10
        self.assertEqual(st.env["x"], 10)
        # no other variables in the state
        self.assertEqual(len(st.env), 1)
    
    def test_if(self):
        prg1 = "x := -4; if x > 10 then x := 10 else x := 6; print_state"
        prg2 = "x := -4; if x > 10 then x := 10 else x := 6; print_state"
        ast1 = ast.parse_string(prg1)
        ast2 = ast.parse_string(prg2)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1,st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(ast1,ast2)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn("x", st.env)
        # x is 20
        self.assertEqual(st.env["x"], 6)
        # no other variables in the state
        self.assertEqual(len(st.env), 1)

    def ttest_while(self):
        prg1 = "x := 1; while x < 10 inv false do x := x + 1; print_state"
        prg2 = "x := 1; while x < 10 inv false do x := x + 1; print_state"
        ast1 = ast.parse_string(prg1)
        ast2 = ast.parse_string(prg2)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1,st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(ast1,ast2)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn("x", st.env)
        # x is 5
        self.assertEqual(st.env["x"], 10)
        # no other variables in the state
        self.assertEqual(len(st.env), 1)

    def test_assert(self):
        prg1 = "x := 5; assert (x > 0); print_state"
        prg2 = "x := 5; assert (x > 0); print_state"
        ast1 = ast.parse_string(prg1)
        ast2 = ast.parse_string(prg2)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1,st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(ast1,ast2)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn("x", st.env)
        # x is 5
        self.assertEqual(st.env["x"], 5)
        # no other variables in the state
        self.assertEqual(len(st.env), 1)

    def test_assume(self):
        prg1 = "x := 10; assume (x > 0); skip"
        prg2 = "x := 10; assume (x > 0); skip"
        ast1 = ast.parse_string(prg1)
        ast2 = ast.parse_string(prg2)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1,st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(ast1,ast2)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn("x", st.env)
        # x is 10
        self.assertEqual(st.env["x"], 10)
        # no other variables in the state
        self.assertEqual(len(st.env), 1)

    def test_havoc(self):
        prg1 = "havoc x, y; print_state"
        prg2 = "havoc x, y; print_state"
        ast1 = ast.parse_string(prg1)
        ast2 = ast.parse_string(prg2)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1,st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(ast1,ast2)
        self.assertIsNotNone(st)
        # x, y is defined
        self.assertIn("x", st.env)
        self.assertIn("y", st.env)
        # no other variables in the state
        self.assertEqual(len(st.env), 2)

    def bool_cons(self):
        prg1 = "if true and false thne skip else print_state"
        ast1 = ast.parse_string(prg1)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1,st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(len(st.env), 0)

    def test_relexp(self):
        prg1 = "if 0 <= 2 and 5 >= 3 then skip else print_state"
        ast1 = ast.parse_string(prg1)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1,st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(len(st.env), 0)

    def test_bexp(self):
        prg1 = "if 2 = 2 or not true then skip"
        ast1 = ast.parse_string(prg1)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1,st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(len(st.env), 0)

    def test_arith_exp(self):
        prg1 = "x := 2; y := x * (5 - 2) / -1; print_state"
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        print(ast1)
        print(repr(ast1))
         # x, y is defined
        self.assertIn("x", st.env)
        self.assertIn("y", st.env)
        # x is 2 and y is -6
        self.assertEqual(st.env["x"], 2)
        self.assertEqual(st.env["y"], -6)
        # no other variables in the state
        self.assertEqual(len(st.env), 2)

    def test_one(self):
        prg1 = "{x := 10}"
        ast1 = ast.parse_string(prg1)
        print(ast1)
        print(repr(ast1))
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)

    def test_empty(self):
        prg1 = "x := 5"
        ast1 = ast.parse_string(prg1)
        print(ast1)
        print(repr(ast1))
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
    
    def test_boolean_exp2(self):
        prg1 = "x := 10; if x <= 11 and x >= 5 then skip else print_state"
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        print(ast1)
        print(repr(ast1))
         # x is defined
        self.assertIn("x", st.env)
         # x is 10
        self.assertEqual(st.env["x"], 10)
        # no other variables in the state
        self.assertEqual(len(st.env), 1)

    def test_multiple_operators(self):
        exp = ast.Exp(["+", "*"], [4, 7])
        self.assertTrue(exp.is_binary())

    def parse_file(self):
        ast1 = ast.parse_file("wlang/test1.prg")
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1, st)
        print(ast1)
        print(repr(ast1))
         # x is defined
        self.assertIn("x", st.env)
         # x is 1
        self.assertEquals(st.env["x"],10)
        # no other variables in the state
        self.assertEquals(len(st.env), 1)

    def test_intVar(self):
        var = ast.IntVar("x")
        print(var)
        print(repr(var))
        mydict = {}
        mydict[var] = 1

    def test_constVar(self):
        var = ast.IntConst(1)
        print(var)
        print(repr(var))
        mydict = {}
        mydict[var] = 1

    def test_print_v(self):
        prg1 = "havoc x"
        ast1 = ast.parse_string(prg1)
        ast1.stmts = None
        print_visitor = ast.PrintVisitor(None)
        print_visitor.visit_StmtList(ast1)

    def test_if_else_path(self):
        prg1 = "if false then skip"
        ast1 = ast.parse_string(prg1)
        interpretor = int.Interpreter()
        st = int.State()
        st = interpretor.run(ast1, st)
        print(ast1)
        print(repr(ast1))
        self.assertEqual(len(st.env), 0)

    def test_assert_else_path(self):
        with self.assertRaises(AssertionError):
            prg1 = "x := 5; \n assert x < 0\n"
            ast1 = ast.parse_string(prg1)
            interp = int.Interpreter()
            st = int.State()
            st.__repr__()
            st = interp.run(ast1, st)
            print(ast1)
            print(repr(ast1))
            # x is defined
            self.assertIn("x", st.env)
            # x is 1
            self.assertEqual(st.env["x"],1)
            # no other variables in the state
            self.assertEqual(len(st.env), 1)

    def if_visitor(self):
        prg1 = "z := 2; if z = 1 then skip"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def while_visitor(self):
        prg1 = "z := 2; while z > 0 do print_state"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def skip_visitor(self):
        prg1 = "skip"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def print_visitor(self):
        prg1 = "print_state"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)
    
    def assume_visitor(self):
        prg1 = "x := 1; assume x > 0"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def assert_visitor(self):
        prg1 = "x := 1; assert x > 0"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def havoc_visitor(self):
        prg1 = "havoc x"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def test_visit_exp_unary(self):
        class CaptureVisitor(ast.PrintVisitor):
            def __init__(self):
                self.output = ""
                super().__init__(out=self)

            def write(self, s):
                self.output += s

        unar_expr = ast.Exp("-", [ast.IntVar("x")])

        cv = CaptureVisitor()

        cv.visit(unar_expr)

        exp_op = "-x"

        self.assertEqual(cv.output.strip(), exp_op)

    def test_WhileLangBuffer (self):
        prg1 = "a ade "
       
        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string(prg1)

        prg1 = "if (a < q) or (b) or (c) and f then skip"

        with self.assertRaises(Exception) as context:
            ast1 = ast.parse_string(prg1)

    def if_visitor(self):
        prg1 = "x := 5; if x = 1 then skip"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def while_visitor(self):
        prg1 = "x := 5; while x > 0 do print_state"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def skip_visitor(self):
        prg1 = "skip"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def print_visitor(self):
        prg1 = "print_state"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)
    
    def assume_visitor(self):
        prg1 = "x := 5; assume x > 0"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def assert_visitor(self):
        prg1 = "x := 5; assert x > 0"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def havoc_visitor(self):
        prg1 = "havoc x"
        ast1 = ast.parse_string(prg1)
        visitor = mockVisitor.StmtVisitorMock()
        visitor.visit(ast1)

    def PrintVisitor_visit_Stmts(self):
        prg1 = "skip; skip"
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        pv = ast.PrintVisitor()
        pv.visit(ast1)
        ast1.stmts = [ast1.stmts[0]]
        pv = ast.PrintVisitor()
        self.assertEqual(pv.visit_StmtList(ast1, indent=0, no_brkt=False), None)