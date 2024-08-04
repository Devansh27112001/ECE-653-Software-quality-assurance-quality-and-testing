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
import z3

from . import ast, sym


class TestSym (unittest.TestCase):
    def test_one(self):
        prg1 = "havoc x; assume x > 10; assert x > 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_two(self):
        prg2 = "havoc y; assume y <= 5; assert y < 10; print_state"
        ast2 = ast.parse_string(prg2)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast2, st)]
        self.assertEqual(len(out), 1)

    def test_three(self):
        prg3 = "havoc z; assume z = 0; assert z = 0; print_state"
        ast3 = ast.parse_string(prg3)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast3, st)]
        self.assertEqual(len(out), 1)
    
    def test_four(self):
        prg4 = "havoc a, b; assume a > b; assert a > 0; print_state"
        ast4 = ast.parse_string(prg4)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast4, st)]
        self.assertEqual(len(out), 1)

    def test_five(self):
        prg5 = "havoc c; if c > 5 then c := c - 1 else c := c + 1; assert c > 0; print_state"
        ast5 = ast.parse_string(prg5)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast5, st)]
        self.assertEqual(len(out), 2)

    def test_six(self):
        prg8 = "havoc f; assume f >= 3; if f > 10 then assert f < 20 else assert f >= 3; print_state"
        ast8 = ast.parse_string(prg8)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast8, st)]
        self.assertEqual(len(out), 2)
        self.assertIsNotNone(out[0].to_smt2())
        self.assertIsNotNone(out[1].to_smt2())
        self.assertIsNotNone(out[0].pick_concerete())
        self.assertIsNotNone(out[1].pick_concerete())

    def test_Aexp(self):
        prg1 = "havoc x; y := x + 2; assume x > 10; assert y > 15; skip"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        solver = z3.Solver()
        st = sym.SymState(solver)
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_rel_exp(self):
        prg1 = "havoc x; y := x + 2; assert y >= x; z := x - 1; assert x > z; w := x; assert w = x"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_bool_exp(self):
        prg1 = "havoc x; assume x > 0; if x < 0 or false then x := x + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)
        self.assertIsNotNone(out[0].pick_concerete())
    
    def test_if(self):
        prg1 = "havoc x, y; if (x > 2 and y < 2) then x := x / 2 else y := y * 2; assume y > x"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_if_2(self):
        prg1 = "havoc x; assume x > 0; if not x <= 0 then x := x + 5 else x := x - 5"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_if_3(self):
        prg1 = "havoc x; assume x > 5; if x > 5 then if x > 8 then y := 2 else y := 3 else y := 4"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 2)

    def test_while(self):
        prg1 = "havoc x; while x > 0 do x := x - 5"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 11)

    def test_while_2(self):
        prg1 = "havoc x; while false or 5 <= 6 do x := x - 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 0)
    
    def test_while_3(self):
        prg1 = "havoc x; assume x > 0; y := x + 5; while y > x do y := y - 2; assert not x = y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_while_4(self):
        prg1 = "x := 2; z := 0; while x > 0 do {y := 2; while y > 0 do {z := z + 1; y := y - 1}; x := x - 1}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_while_5(self):
        prg1 = "x := 1; while x > 30 do x := x + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_if_into_while(self):
        prg1 = "havoc x; if x > 0 then {y := 5; while y > 0 do y := y - 2} else skip"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 2)

    def test_while_into_if(self):
        prg1 = "x := 5; havoc y; while x > 0 do {if y < x then y := y + 2 else y := y - 1; x := x - 2}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 4)

    # def test_while_symbolic_execution_engine_diverges(self):
    #     prg1 = "havoc x, y; while x > 0 do {while y > x do {y := y / 2 - 1}; x := x / 2 - 1}"
    #     ast1 = ast.parse_string(prg1)
    #     engine = sym.SymExec()
    #     st = sym.SymState()
    #     out = [s for s in engine.run(ast1, st)]
    #     self.assertEqual(len(out), 700)

    def while_invariant(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv c <= y and r = x + c do { r := r + 1; c := c + 1}; assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_while_inv2(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r = x do { r := r + 1; c := c + 1}; assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_while_inv3(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r = x + 1 do { r := r + 1; c := c + 1}; assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 0)

    def test_while_inv4(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < 0 inv c >= y do { r := r + 1; c := c + 1}; assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)
    
    def test_while_inv5(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while true inv c >= y do { r := r + 1; c := c + 1}; assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 0)

    def test_while_inv6(self):
        prg1 = "havoc x, y; assume y >= 0; a := 0; b := 0; c := 0; r := x; while c < y inv c <= y and r = x + a * c - b * c do { r := r + a; r := r - b; c := c + 1 }; assert r = x + a * y - b * y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)
    
   

   
