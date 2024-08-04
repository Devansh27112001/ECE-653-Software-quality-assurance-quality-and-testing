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

import sys
import io 
import z3
import time 

from . import ast, int
from functools import reduce
from . import undef_visitor


class SymState_Assumption(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        self.added_expressions = set()
        self.expression_counter = 0

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        for expressions in exp:
            unique_identifier = f'tracking_{self.expression_counter}_{hash(expressions)}'
            self.expression_counter += 1

            if expressions not in self.added_expressions:
                tracked_variable = z3.Bool(unique_identifier)
                self._solver.assert_and_track(expressions, tracked_variable)
                self.path.append(tracked_variable)
                self.added_expressions.add(expressions)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concrete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st

    def fork(self, assumptions):
        """Fork the current state into two identical states that can evolve separately"""
        child_state = SymState_Assumption()
        child_state.env = self.env.copy()

        for expr in self.path:
            child_state.add_pc(expr)

        
        child_state.add_pc(assumptions)
        return child_state 

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()

class SymExec_Assumption(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        return self.visit(ast, state=state)

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs
        assert False

    
    def visit_BExp(self, node, *args, **kwargs):
        children = [self.visit(a, *args, **kwargs) for a in node.args]
        if node.op == "not":
            assert node.is_unary()
            assert len(children) == 1
            return z3.Not(children[0])
        fn = None 
        cond = None 
    
        if node.op == "and":
            fn = lambda x, y: z3.And(x,y)
            cond = True
        
        elif node.op == "or":
            fn = lambda x,y: z3.Or(x, y) 
            cond = False
        assert fn is not None
        return reduce(fn, children, cond)

    def visit_AExp(self, node, *args, **kwargs):
        children = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if node.op == "+":
            fn = lambda x, y: x + y

        elif node.op == "-":
            fn = lambda x, y: x - y

        elif node.op == "*":
            fn = lambda x, y: x * y

        elif node.op == "/":
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, children)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return [kwargs['state']]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        print([kwargs['state']])
        return [kwargs['state']]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        symbol = self.visit(node.rhs, *args, **kwargs)
        variable = node.lhs.name
        state = kwargs['state']

        if variable not in state.env:
            state.env[variable] = z3.FreshInt(variable)
        state.env[variable] = symbol
        return [state]

    def visit_IfStmt(self, node, *args, **kwargs):
        output_state = []
        conditions = self.visit(node.cond, *args, **kwargs)
        prev_state = kwargs['state']

        "Forking the prev_state assuming that the condtion is true" 
        true_state = prev_state.fork(conditions)
        true_state.add_pc(conditions)

        if not true_state.is_empty():
            output_state.extend(self.visit(node.then_stmt, state = true_state))

        "Forking the prev_state assuming that the condtion is false " 
        false_state = prev_state.fork(z3.Not(conditions))
        false_state.add_pc(z3.Not(conditions))
        if not false_state.is_empty():
            if node.has_else():
                output_state.extend(self.visit(node.else_stmt, state = false_state))
            else:
                output_state.extend([false_state])

        return output_state
            



    
    def visit_WhileStmt(self, node, *args, **kwargs):
        output_states = []
        current_state = kwargs["state"]
        condition = self.visit(node.cond, *args, **kwargs)
    

        assert_pass = current_state.fork(condition)
        assert_fail = current_state.fork(z3.Not(condition))

        assert_pass.add_pc(condition)
        assert_fail.add_pc(condition)


        if not assert_fail.is_empty():
            output_states.append(assert_fail)

        "Checking if the invariant fails in the initiation stage"
        if node.inv is not None:
            before_inv = self.visit(node.inv, *args, **kwargs)
            inv_assertPass = assert_pass.fork(before_inv)
            inv_assertFail = assert_pass.fork(z3.Not(before_inv))

            inv_assertPass.add_pc(before_inv)
            inv_assertFail.add_pc(z3.Not(before_inv))
        
            if not inv_assertFail.is_empty():
                error = f"Error: The invariant might fail when entering the loop: assertion may be false for {assert_pass} on {node.inv} if {assert_fail.pick_concrete()}"
                print(error)
                inv_assertFail.mk_error()
                output_states.append(inv_assertFail)

            if not inv_assertPass.is_empty():
                assert_pass = inv_assertPass

            else:
                return output_states


        if not assert_pass.is_empty():
            after_body_states = self.visit(node.body, state = assert_pass)
            for state in after_body_states:
                if node.inv is not None:
                    inv = self.visit(node.inv, *args, **kwargs)
                    pass_body = state.fork(inv)
                    fail_body = state.fork(z3.Not(inv))

                    pass_body.add_pc(inv)
                    fail_body.add_pc(z3.Not(inv))

                    if not fail_body.is_empty():
                        error = f"Error: The invariant might fail when entering the loop: assertion may be false for {assert_pass} on {node.inv} if {assert_fail.pick_concrete()}"
                        print(error)
                        fail_body.mk_error()
                        output_states.append(fail_body)

                    if not pass_body.is_empty():
                        pass_body.add_pc(z3.BoolVal(False))
                        output_states.append(pass_body)

                else:
                    output_states.append(state)
        return output_states


    def visit_AssertStmt(self, node, *args, **kwargs):
        conditions = self.visit(node.cond, *args, **kwargs)
        st = kwargs['state']
  
        false_state = st.fork(z3.Not(conditions))
        #if the assert condition fails
        false_state.add_pc(z3.Not(conditions))
        if not false_state.is_empty():
            print(f"The condition {node.cond} wasn't met due to the concrete values picked")
            print("the concrete spoil is", false_state.pick_concrete())
            false_state.mk_error()

        true_state = st.fork(conditions)
        #if the assert condition passes
        true_state.add_pc(conditions)
        if not true_state.is_empty():
            return [true_state]
        
        else:
            return []

    def visit_AssumeStmt(self, node, *args, **kwargs):
        conditions = self.visit(node.cond, *args, **kwargs)
        state = kwargs['state']
        state.add_pc(conditions)
        if state.is_empty(): 
            return []
        else: 
            return [state]
        

    def visit_HavocStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        for variable in node.vars:
            state.env[variable.name] = z3.FreshInt(variable.name)
        return [state]

    def visit_StmtList(self, node, *args, **kwargs):
        current_states = [kwargs['state']]
        for stmt in node.stmts:
            processed_states = []
            for state in current_states:
                states = self.visit(stmt, state=state)
                processed_states.extend(states)
            current_states = processed_states
        return current_states


def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = SymState_Assumption()
    sym = SymExec_Assumption()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
