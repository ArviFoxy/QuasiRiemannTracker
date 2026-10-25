"""Literal-level knobs for the exact final-return certificate.

`instrumented()` returns a copy of `repeated-marks/cert_return.py` in which every numeric literal in
the formula functions becomes `KN(name, value)`. A knob's value is `value*(1 + REL.get(name, 0))`.
Names are `function:line:col:value`, so they point back at the source line.
Fractions are folded at rewrite time (`Fr(13, 75)` -> one knob); exponents and tuple keys are kept.
"""
import ast, os, sys, types
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
RM = os.path.join(HERE, '..', 'repeated-marks')
TARGETS = {'branch_affine', 'branch_old', 'admission_polys', 'geometry', 'edges', 'return_poly',
           'receipt'}

def _const_value(node):
    """Fold an expression built only from int literals, unary minus, +,-,*,/,** into a Fraction."""
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
        return Fr(node.value)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        v = _const_value(node.operand)
        return None if v is None else -v
    if isinstance(node, ast.BinOp):
        a, b = _const_value(node.left), _const_value(node.right)
        if a is None or b is None: return None
        if isinstance(node.op, ast.Pow): return a**int(b)
        if isinstance(node.op, ast.Add): return a + b
        if isinstance(node.op, ast.Sub): return a - b
        if isinstance(node.op, ast.Mult): return a*b
        if isinstance(node.op, ast.Div): return a/b
    return None

class Rewriter(ast.NodeTransformer):
    def __init__(self):
        self.func = None; self.knobs = {}
    def _knob(self, node, value):
        name = f"{self.func}:{node.lineno}:{node.col_offset}:{value}"
        self.knobs[name] = value
        return ast.copy_location(ast.Call(func=ast.Name('KN', ast.Load()),
            args=[ast.Constant(name), ast.Call(func=ast.Name('Fr', ast.Load()),
                  args=[ast.Constant(value.numerator), ast.Constant(value.denominator)], keywords=[])],
            keywords=[]), node)
    def visit_FunctionDef(self, node):
        if node.name not in TARGETS: return node
        self.func = node.name
        self.generic_visit(node)
        self.func = None
        return node
    def visit_Call(self, node):
        if self.func and isinstance(node.func, ast.Name) and node.func.id == 'Fr' and node.args:
            vals = [_const_value(a) for a in node.args]
            if all(v is not None for v in vals):
                v = vals[0] if len(vals) == 1 else vals[0]/vals[1]
                return self._knob(node, v)
        if self.func and isinstance(node.func, ast.Name) and node.func.id in ('const', 'smul'):
            a0 = node.args[0]
            v = _const_value(a0) if not isinstance(a0, ast.Call) else None
            if v is not None:
                node.args[0] = self._knob(a0, v)
                node.args[1:] = [self.visit(a) for a in node.args[1:]]
                return node
        self.generic_visit(node)
        return node
    def visit_BinOp(self, node):
        if not self.func: return self.generic_visit(node)
        if isinstance(node.op, ast.Pow):           # keep exponents literal
            return node
        for side in ('left', 'right'):
            child = getattr(node, side)
            v = _const_value(child) if not isinstance(child, ast.Call) else None
            if v is not None and not (isinstance(child, ast.BinOp) and isinstance(child.op, ast.Pow)):
                setattr(node, side, self._knob(child, v))
            else:
                setattr(node, side, self.visit(child))
        return node
    def visit_Subscript(self, node):               # dict keys / indices stay literal
        return node
    def visit_Tuple(self, node):
        return node

REL = {}
MODULE_KNOBS = {'V:5/6': Fr(5, 6), 'M_MINUS': Fr(2, 5), 'M_PLUS': Fr(11, 25), 'S_MINUS': Fr(17, 500),
                'M_H:17/500': Fr(17, 500), 'R0': Fr(1, 10**9)}
def apply_module_knobs(mod):
    g = lambda k: KN(k, MODULE_KNOBS[k])
    mod.V = mod.sub(mod.const(g('V:5/6')), mod.DEL)
    mod.M_MINUS, mod.M_PLUS, mod.S_MINUS = g('M_MINUS'), g('M_PLUS'), g('S_MINUS')
    mod.M_H = (1 - mod.K_I*g('M_H:17/500'))/2
    mod.R0 = g('R0')
def KN(name, value):
    r = REL.get(name)
    return value if not r else value*(1 + Fr(r).limit_denominator(10**9))

def instrumented():
    sys.path.insert(0, RM)
    src = open(os.path.join(RM, 'cert_return.py')).read()
    tree = ast.parse(src)
    rw = Rewriter()
    tree = rw.visit(tree)
    ast.fix_missing_locations(tree)
    mod = types.ModuleType('cert_return_knobs')
    mod.__file__ = os.path.join(RM, 'cert_return.py')
    mod.KN = KN
    exec(compile(tree, mod.__file__, 'exec'), mod.__dict__)
    mod.__dict__['__name__'] = 'cert_return_knobs'
    knobs = dict(rw.knobs); knobs.update(MODULE_KNOBS)
    return mod, knobs

if __name__ == '__main__':
    mod, knobs = instrumented()
    print(len(knobs), 'knobs')
    for k in list(knobs)[:400]: print(k)
