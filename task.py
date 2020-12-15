import z3
import lark

def interp(tree, lookup):
    op = tree.data
    if op in ('add', 'sub', 'mul', 'div', 'shl', 'shr',
    'gt', 'lt', 'eq', 'neq', 'and', 'or'):
        lhs = interp(tree.children[0], lookup)
        rhs = interp(tree.children[1], lookup)
        if op == 'add':
            return lhs + rhs
        elif op == 'sub':
            return lhs - rhs
        elif op == 'mul':
            return lhs * rhs
        elif op == 'div':
            return lhs / rhs
        elif op == 'shl':
            return lhs << rhs
        elif op == 'shr':
            return lhs >> rhs
        elif op == 'gt':
            return z3.If(lhs > rhs, z3.BitVecVal(1, 8), z3.BitVecVal(0, 8))
        elif op == 'lt':
            return z3.If(lhs < rhs, z3.BitVecVal(1, 8), z3.BitVecVal(0, 8))
        elif op == 'eq':
            return z3.If(lhs == rhs, z3.BitVecVal(1, 8), z3.BitVecVal(0, 8))
        elif op == 'neq':
            return z3.If(lhs != rhs, z3.BitVecVal(1, 8), z3.BitVecVal(0, 8))
        elif op == 'and':
            return lhs & rhs
        elif op == 'or':
            return lhs | rhs
        elif op == 'pow':
            return lhs ** rhs
    elif op == 'neg':
        sub = interp(tree.children[0], lookup)
        return -sub
    elif op == 'num':
        return int(tree.children[0])
    elif op == 'true':
        return BitVecVal(1, 1)
    elif op == 'false':
        return BitVecVal(0, 1)
    elif op == 'var':
        return lookup(tree.children[0])
    elif op == 'if':
        cond = interp(tree.children[0], lookup)
        true = interp(tree.children[1], lookup)
        false = interp(tree.children[2], lookup)
        return (cond != 0) * true + (cond == 0) * false

def z3_expr(tree, vars=None):

    vars = dict(vars) if vars else {}

    def get_var(name):
        if name in vars:
            return vars[name]
        else:
            v = z3.BitVec(name, 8)
            vars[name] = v
            return v

    return interp(tree, get_var), vars

def solve(formula):
    s = z3.Solver()
    s.add(formula)
    s.check()
    return s.model()

GRAMMAR = """
?start : sum
    | sum "?" sum ":" sum -> if
    | start "and" sum -> and
    | start "or" sum -> or
    | start "**" sum -> pow

?sum : term
    | sum "==" term -> eq
    | sum "!=" term -> neq
    | sum "<" term -> lt
    | sum ">" term -> gt
    | sum "+" term -> add
    | sum "-" term -> sub

?term: item
    | term "*" item -> mul
    | term "/" item -> div
    | term ">>" item -> shr
    | term "<<" item -> shl

?item: NUMBER -> num
    | "-" item -> neg
    | CNAME -> var
    | "True" -> true
    | "False" -> false
    | "(" start ")"


%import common.NUMBER
%import common.WS
%import common.CNAME
%ignore WS
""".strip()

if __name__ == '__main__':
    z = z3.Int('z')
    n = z3.Int('n')
    r = z3.Int('r')
    #print(solve(z3.And(z > 1, z3.And(n > 1, z * n == 2491))))
    #print(solve(z3.And(z == 71, z3.And(n >=1, z3.And(r >= 1, z ** 2 + n ** 2 ==r**2)))))
    #print(solve(z3.And(z > 0, z3.And(n > 0, z3.And(r > 0, z ** 3 + n ** 3 == r**3)))))
    # formula = z3.Int('x') * 7 /6

    #z = z3.Int('z')
    #n = z3.Int('n')

    #f = z3.ForAll([z], z * n == z)
    #print(solve(y << 3 == 40))

    #x = z3.BitVec('x', 8)
    #slow_expr = x * 4

    #h = z3.BitVec('h', 8)
    #fast_expr = x << h

    #goal = z3.ForAll([x], slow_expr == fast_expr)

    parser = lark.Lark(GRAMMAR)

    #slow_prog, vars1 = z3_expr(parser.parse("x * 9"))
    #fast_prog, vars2 = z3_expr(parser.parse("x << (h1 ? x : h2) + (h3 ? x : h4)"), vars1)

    slow_prog, vars1 = z3_expr(parser.parse("True"))
    fast_prog, vars2 = z3_expr(parser.parse("h1 > 1 and h2 > 1 and h1 * h2 == 2491"), vars1)

    plain_vars = {k: v for k, v in vars2.items() if not k.startswith('h')}

    goal = z3.ForAll(
        list(plain_vars.values()),
        slow_prog == fast_prog,
    )

    print(solve(goal))

    #tree = parser.parse("(x * 3) << y")
    #env = {'x': 2, 'y': 9}
    #print(interp(tree, lambda v: env[v]))
    #print(interp(tree, lambda v: z3.BitVec(v, 8)))


    #print(solve(goal))
