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
from traitlets import Bool
import z3

from . import ast, int
from functools import reduce
from . import undef_visitor

class SymState_Scope(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

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

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        
        self._solver.push()  # We are creating a new scope here

        child = SymState_Scope(self._solver)
        child.env = dict(self.env)
        # There is no need to add the path conditions again as they are already in the current scope.

        return (self, child)

    def revert(self):
        """Reverts the state to the previous scope"""
        self._solver.pop()
        

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

class SymExec_Scope(ast.AstVisitor):
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
        base = None 
    
        if node.op == "and":
            fn = lambda x, y: z3.And(x,y)
            base = True
        
        elif node.op == "or":
            fn = lambda x,y: z3.Or(x, y) 
            base = False
        assert fn is not None
        return reduce(fn, children, base)


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
        "Get the previous states"
        output_state = []
        conditions = self.visit(node.cond, *args, **kwargs)
        st = kwargs['state']
        
        "Adding a new scope to the top"
        st.fork()
        true_state = st
        true_state.add_pc(conditions)

        "If path cond. is feasible or satisfiable, add it to the output_state"
        if not true_state.is_empty():
            output_state.extend(self.visit(node.then_stmt, state = true_state))
        "Reverting back to the top of the stack, and add an another new scope"
        st.revert()
        st.fork()
        false_state = st
        false_state.add_pc(z3.Not(conditions))
        
        "If path cond. is feasible or satisfiable, check if it has an else condition. Execute it ad add it to the output_state"
        if not false_state.is_empty():
            if node.has_else():
                output_state.extend(self.visit(node.else_stmt, state = false_state))
            else:
                output_state.extend([false_state])

        st.revert()
        return output_state
    
    def visit_WhileStmt(self, node, *args, **kwargs):
        output_state = []
        current_state = kwargs["state"]
        condition = self.visit(node.cond, *args, state = current_state)
        current_state.fork()    

        assert_pass = current_state
        assert_pass.add_pc(condition)
        if assert_pass.is_empty():
            current_state.revert()
            return [current_state]
        
        current_state.revert()

        if node.inv is not None:
            invLoop_before = self.visit(node.inv, *args, **kwargs)
            current_state.fork()
            assert_pass = current_state
            assert_pass.add_pc(invLoop_before)
            current_state.revert()
            current_state.fork()
            assert_fail = current_state
            assert_fail.add_pc(z3.Not(invLoop_before))
            if not assert_fail.is_empty():
                error = f"Error: The invariant might fail when entering the loop: assertion may be false for {assert_pass} on {node.inv} if {assert_fail.pick_concrete()}"
                print(error)
                assert_fail.mk_error()

            current_state.revert()
            assert_pass = current_state

        else:
            assert_pass = current_state

        
        undefVisitorInt = undef_visitor.UndefVisitor()
        undefVisitorInt.check(node.body)
        variables = undefVisitorInt.get_defs()
        for variable in variables:
            assert_pass.env[variable.name] = z3.FreshInt(variable.name)
            condition = self.visit(node.cond, *args, state=assert_pass)
            assert_pass.fork()
            cond_satisfied = assert_pass
            cond_satisfied.add_pc(condition)
            assert_pass.revert()
            assert_pass.fork()
            cond_notSatisfied = assert_pass
            cond_notSatisfied.add_pc(z3.Not(condition))

            if not cond_notSatisfied.is_empty():
                output_state.append(cond_notSatisfied)

            if not cond_satisfied.is_empty():
                after_condition_satisfied = self.visit(node.body, state = cond_satisfied)
                for state in after_condition_satisfied:
                    state.fork()
                    conditonPass_body = state

                    if node.inv is not None:
                        invariant = self.visit(node.inv, *args, **kwargs)
                        conditonPass_body.add_pc(invariant)
                        state.revert()
                        state.fork()
                        conditionFail_body = state
                        conditionFail_body.add_pc(z3.Not(invariant))

                        if not conditionFail_body.is_empty():
                            error = f"error: invariant may not hold in loop body: maybe false {conditonPass_body} on {node.inv} if {conditionFail_body.pick_concrete()}"
                            print(error)
                            conditionFail_body.mk_error()

                    if not conditonPass_body.is_empty():
                        conditonPass_body.add_pc(False)
                        output_state.append(conditonPass_body)
        return output_state
    
   



        # # Add an initial condition to the stat

        # # Simulate the while loop for a fixed number of iterations (e.g., 10)
        # for iterations in range(0, 11):
        #     starting_states = []

        #     for each_state in intermidiates:
        #         st1,st2 = each_state.fork()
        #         # In the first iteration, negate the condition
        #         condition = self.visit(node.cond, *args, state = each_state) 
        #         st2.add_pc(condition)
        #         st1.add_pc(z3.Not(condition))

        #         if not st1.is_empty():
        #             current_state.append(st1)

        #         # Fork the state for each iteration
        #         if not st2.is_empty() and iterations != 10:
        #             body_state = self.visit(node.body, state = st2)
        #             starting_states.extend(body_state)

        #     intermidiates = starting_states
        # current_state.extend(intermidiates)
        # return current_state

    def visit_AssertStmt(self, node, *args, **kwargs):
        conditions = self.visit(node.cond, *args, **kwargs)
        st = kwargs['state']
        st.fork()
        assert_pass_state = st

        st.revert()
        st.fork()
        assert_fail_state = st

        #if the assert condition fails
        assert_fail_state.add_pc(z3.Not(conditions))
        if not assert_fail_state.is_empty():
            print(f"The condition {node.cond} wasn't met due to the concrete values picked")
            print("the concrete spoil is", assert_pass_state.pick_concrete())
            assert_fail_state.mk_error()

        assert_fail_state.revert()

        #if the assert condition passes
        assert_pass_state.add_pc(conditions)
        if not assert_pass_state.is_empty():
            return [assert_pass_state]
        
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
    st = SymState_Scope()
    sym = SymExec_Scope()

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
