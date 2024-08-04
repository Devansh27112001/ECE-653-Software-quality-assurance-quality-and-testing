import unittest

from . import ast, stats_visitor


class TestStatsVisitor(unittest.TestCase):
    def test_one(self):
        prg1 = "x := 10; print_state"
        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEqual(sv.get_num_stmts(), 2)
        self.assertEqual(sv.get_num_vars(), 1)

    def test_assign(self):
        prg1= "x := 1; y := 5"
        ast1 = ast.parse_string(prg1)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        self.assertEqual(sv.get_num_stmts(), 2)
        self.assertEqual(sv.get_num_vars(), 2)

    def test_ifStmt(self):
        prg1 = "if x > 2 then y := 1 else y := 2"
        ast1 = ast.parse_string(prg1)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        self.assertEqual(sv.get_num_stmts(), 3)
        self.assertEqual(sv.get_num_vars(), 2)

    def test_whileStmt(self):
        prg1 = "while x > 1 do x := x - 1"
        ast1 = ast.parse_string(prg1)        
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        self.assertEqual(sv.get_num_stmts(), 2)
        self.assertEqual(sv.get_num_vars(), 1)
    
    def test_assertStmt(self):
        prg1 = "assert x = 5"
        ast1 = ast.parse_string(prg1)        
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)        
        self.assertEqual(sv.get_num_stmts(), 1)
        self.assertEqual(sv.get_num_vars(), 1)
    
    def test_assumeStmt(self):
        prg1 = "assume x = 5"
        ast1 = ast.parse_string(prg1)        
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)        
        self.assertEqual(sv.get_num_stmts(), 1)
        self.assertEqual(sv.get_num_vars(), 1)
    
    def test_havocStmt(self):
        prg1 = "havoc x, y"
        ast1 = ast.parse_string(prg1)        
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)        
        self.assertEqual(sv.get_num_stmts(), 1)
        self.assertEqual(sv.get_num_vars(), 0)

    def test_uexp(self):
        prg1 = "a := b"
        ast1 = ast.parse_string(prg1)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)        
        self.assertEqual(sv.get_num_stmts(), 1)
        self.assertEqual(sv.get_num_vars(), 2)

    def test_bexp(self):
        prg1 = "x := y + z"
        ast1 = ast.parse_string(prg1)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        self.assertEqual(sv.get_num_stmts(), 1)
        self.assertEqual(sv.get_num_vars(), 3)

    def visit_StmtList(self, node, *args, **kwargs):
        for st in node.stmts:
            self.visit(st)
        pass