from . import ast


class StmtVisitorMock(ast.AstVisitor):
    def __init__(self):
        super(StmtVisitorMock, self).__init__()

    def visit_StmtList(self, node, *args, **kwargs):
        for s in node.stmts:
            self.visit(s)

    def visit_Stmt(self, node, *args, **kwargs):
        pass

    def visit_AsgnStmt(self, node, *args, **kwargs):
        super().visit_AsgnStmt(node, *args, **kwargs)
        super().visit_IntVar(node, *args, **kwargs)

    def visit_Exp(self, node, *args, **kwargs):
        pass

    def visit_Const(self, node, *args, **kwargs):
        pass