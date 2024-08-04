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

from . import ast, sym_assumptions
import z3





class TestSym (unittest.TestCase):
    def test_1(self):
        prg1 = "x:=1; print_state; skip"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_extra1(self):
        st = sym_assumptions.SymState_Assumption()
        st.is_error()
        st.__repr__()   
        st.to_smt2()


    def test_extra2(self):
        st = sym_assumptions.SymState_Assumption()
        r = z3.IntVal(1) > z3.IntVal(1)
        st._solver.add(r)
        st.pick_concrete()

    def test_2(self):
        prg1 = "x:=10; while x>9 do {x:=x-1}"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_3(self):
        prg1 = "havoc x ; if x > 10 then { x := x + 1; z := 10}  else y := x + 1  x := z + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 2)
    
    def test_5(self):
        prg1 = "x:=50; assert x=10; assert x=5"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 0)
    
    def test_6(self):
        prg1 = "x:=50; assert x=50" 
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 1)

    def test_7(self):
        prg1 = "x:=8; while (not (x=8)) do x:=x-1"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertEqual(len(out), 0)

    def test_8(self):
        prg1 = "x:=10; y:=20; assert x=10 and y=20"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        [s for s in engine.run(ast1, st)]
    
    def test_9(self):
        prg1 = "x:=10; y:=5; assert x=10 or y=10"  
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        [s for s in engine.run(ast1, st)]

    def test_10(self):
        prg1 = "x:=20; y:=10; z := x / y" 
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)

    def test_11(self):
        prg1 = "x:=20; y:=10; z := x * y"  
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)

    def test_12(self):
        prg1 = "x:=11; y:=10; assert x > y"  
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)

    def test_13(self):
        prg1 = "x:=10; y:=10; assert x >= y"  
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)

    def test_14(self):
        prg1 = "x:=9; y:=10; assert x < y"  
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)


    def test_15(self):
        prg1 = "x:=10; y:=10; assert x <= y" 
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)
    
    def test_16(self):
        prg1 = "assert true"  
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)

    def test_17(self):
        prg1 = ast.AExp(['/'], [ast.IntConst("5"), ast.IntConst("9")])
        prg2 = ast.AExp(['/'], [ast.IntConst("5"), ast.IntConst("7")])
        Ast_conver = ast.BExp(["?"], [prg1,prg2])
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        with self.assertRaises(AssertionError):
            [s for s in engine.run(Ast_conver, st)]
        
    def test_18(self):
        prg1 = ast.AExp(['-'], [ast.IntConst("16"), ast.IntConst("12")])
        prg2 = ast.AExp(['-'], [ast.IntConst("12"), ast.IntConst("1")])
        Ast_conver = ast.RelExp(prg1, ["?"], prg2)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        with self.assertRaises(AssertionError):
            [s for s in engine.run(Ast_conver, st)]

    def test_wrong_inv_inside(self):
        prg = "x := 0; while (x < 20) inv (x < 10) do { x := x + 2}"
        ast1 = ast.parse_string(prg)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertTrue(any(s.is_error for s in out))
    
    def test_wrong_inv_before(self):
        prg = "x := 11; while (x < 20) inv (x < 10) do { x := x + 1}"
        ast1 = ast.parse_string(prg)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertTrue(any(s.is_error for s in out))

    def test_dafny_program_Question_4B(self):
        prg1 = "havoc x; havoc y; assume y >= 0; c := 0; r := x; while (c < y) inv ((r = x + c) and (c <= y)) do { r := r + 1; c := c + 1 } assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        out = [s for s in engine.run(ast1, st)]
        self.assertFalse(all(not s.is_error for s in out))

    def test_sum_numbers(self):
        prg1 = "havoc n; assume n >= 0; sum := 0; i := 1; while (i <= n) inv ((sum = ((i - 1) * i) / 2) and (i <= n + 1)) do { sum := sum + i; i := i + 1}; assert sum = (n * (n + 1)) / 2"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)
    
    def test_sum_numbers_2(self):
        prg1 = "havoc n; assume n >= 1; sum := 0; i := 1; while i <= n inv i <= n + 1 and sum = i * (i - 1) / 2 do {j := 1; temp_sum := 0; while (j <= i) inv j <= i + 1 and temp_sum = j * (j - 1) / 2 do {temp_sum := temp_sum + j; j := j + 1}; sum := sum + temp_sum; i := i + 1}; assert sum = n * (n + 1) / 2"
        ast1 = ast.parse_string(prg1)
        engine = sym_assumptions.SymExec_Assumption()
        st = sym_assumptions.SymState_Assumption()
        engine.run(ast1, st)










    




        



