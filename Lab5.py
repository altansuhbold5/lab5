import random
from functools import reduce
from itertools import combinations, product

TT_LIMIT = 200_000
RES_LIMIT = 100_000


def Sym(n): return ('sym', n)
def Not(a): return ('not', a)
def And(a, b): return ('and', a, b)
def Or(a, b): return ('or', a, b)
def Imp(a, b): return ('imp', a, b)
def Iff(a, b): return ('iff', a, b)


def symbols(s):
    if s[0] == 'sym':
        return {s[1]}
    return set().union(*(symbols(c) for c in s[1:]))

def to_str(s):
    if s[0] == 'sym':
        return s[1]
    if s[0] == 'not':
        return '~' + to_str(s[1])
    op = {'and': '&', 'or': '|', 'imp': '=>', 'iff': '<=>'}[s[0]]
    return f"({to_str(s[1])} {op} {to_str(s[2])})"

def pl_true(s, model):
    op = s[0]
    if op == 'sym':
        return model[s[1]]
    if op == 'not':
        return not pl_true(s[1], model)
    a = pl_true(s[1], model)
    b = pl_true(s[2], model)
    if op == 'and':
        return a and b
    if op == 'or':
        return a or b
    if op == 'imp':
        return (not a) or b
    if op == 'iff':
        return a == b


def all_models(syms):
    for vals in product([True, False], repeat=len(syms)):
        yield dict(zip(syms, vals))


def tt_entails(kb, alpha, limit=TT_LIMIT):
    syms = sorted(symbols(kb) | symbols(alpha))
    count = 0
    for m in all_models(syms):
        count += 1
        if count > limit:
            return None, count
        if pl_true(kb, m) and not pl_true(alpha, m):
            return False, count
    return True, count


def is_valid(s):
    return all(pl_true(s, m) for m in all_models(sorted(symbols(s))))


def is_satisfiable(s):
    return any(pl_true(s, m) for m in all_models(sorted(symbols(s))))


def print_truth_table(s):
    syms = sorted(symbols(s))
    print(" | ".join(syms) + " | " + to_str(s))
    for vals in product([True, False], repeat=len(syms)):
        m = dict(zip(syms, vals))
        row = " | ".join("T" if m[x] else "F" for x in syms)
        print(row + " | " + ("T" if pl_true(s, m) else "F"))


def _rebuild(s, f):
    if s[0] == 'sym':
        return s
    return (s[0],) + tuple(f(c) for c in s[1:])


def eliminate_iff(s):
    if s[0] == 'iff':
        a = eliminate_iff(s[1])
        b = eliminate_iff(s[2])
        return And(Imp(a, b), Imp(b, a))
    return _rebuild(s, eliminate_iff)


def eliminate_imp(s):
    if s[0] == 'imp':
        a = eliminate_imp(s[1])
        b = eliminate_imp(s[2])
        return Or(Not(a), b)
    return _rebuild(s, eliminate_imp)


def push_not(s):
    if s[0] == 'not':
        t = s[1]
        if t[0] == 'sym':
            return s
        if t[0] == 'not':
            return push_not(t[1])
        if t[0] == 'and':
            return Or(push_not(Not(t[1])), push_not(Not(t[2])))
        if t[0] == 'or':
            return And(push_not(Not(t[1])), push_not(Not(t[2])))
    return _rebuild(s, push_not)


def distribute(s):
    if s[0] == 'and':
        return And(distribute(s[1]), distribute(s[2]))
    if s[0] == 'or':
        a = distribute(s[1])
        b = distribute(s[2])
        if a[0] == 'and':
            return And(distribute(Or(a[1], b)), distribute(Or(a[2], b)))
        if b[0] == 'and':
            return And(distribute(Or(a, b[1])), distribute(Or(a, b[2])))
        return Or(a, b)
    return s


def to_cnf(s):
    return distribute(push_not(eliminate_imp(eliminate_iff(s))))


def conjuncts(s):
    if s[0] == 'and':
        return conjuncts(s[1]) + conjuncts(s[2])
    return [s]


def disjuncts(s):
    if s[0] == 'or':
        return disjuncts(s[1]) + disjuncts(s[2])
    return [s]


def lit_of(s):
    if s[0] == 'sym':
        return s[1]
    if s[0] == 'not' and s[1][0] == 'sym':
        return '~' + s[1][1]
    raise ValueError("CNF биш өгүүлбэр")


def neg(lit):
    return lit[1:] if lit.startswith('~') else '~' + lit


def lit_name(lit):
    return lit[1:] if lit.startswith('~') else lit


def to_clauses(s):
    clauses = set()
    for c in conjuncts(s):
        cl = frozenset(lit_of(d) for d in disjuncts(c))
        if any(neg(l) in cl for l in cl):
            continue
        clauses.add(cl)
    return clauses


def resolve(ci, cj):
    out = []
    for lit in ci:
        if neg(lit) in cj:
            new = (ci - {lit}) | (cj - {neg(lit)})
            if any(neg(l) in new for l in new):
                continue
            out.append(frozenset(new))
    return out


def refute(clauses, limit=RES_LIMIT):
    clist = []
    cset = set()
    for c in clauses:
        if c not in cset:
            clist.append(c)
            cset.add(c)
    count = 0
    i = 0
    while i < len(clist):
        for j in range(i):
            for r in resolve(clist[i], clist[j]):
                count += 1
                if count > limit:
                    return None, count
                if not r:
                    return True, count
                if r not in cset:
                    cset.add(r)
                    clist.append(r)
        i += 1
    return False, count


def pl_resolution(kb_clauses, alpha):
    clauses = set(kb_clauses) | to_clauses(to_cnf(Not(alpha)))
    return refute(clauses)


def lit_val(lit, model):
    if lit.startswith('~'):
        v = model.get(lit[1:])
        return None if v is None else not v
    return model.get(lit)


def clause_sat(c, model):
    return any(lit_val(l, model) is True for l in c)


def clause_false(c, model):
    return all(lit_val(l, model) is False for l in c)


def find_pure_symbol(symbols_, clauses, model):
    pos, negs = set(), set()
    for c in clauses:
        if clause_sat(c, model):
            continue
        for l in c:
            if lit_val(l, model) is None:
                (negs if l.startswith('~') else pos).add(lit_name(l))
    for s in symbols_:
        if s in model:
            continue
        if s in pos and s not in negs:
            return s, True
        if s in negs and s not in pos:
            return s, False
    return None


def find_unit_clause(clauses, model):
    for c in clauses:
        if clause_sat(c, model):
            continue
        un = [l for l in c if lit_val(l, model) is None]
        if len(un) == 1:
            l = un[0]
            return (l[1:], False) if l.startswith('~') else (l, True)
    return None


def dpll(clauses, symbols_, model, stats):
    stats['calls'] += 1
    if any(clause_false(c, model) for c in clauses):
        return None
    if all(clause_sat(c, model) for c in clauses):
        return model
    symbols_ = [s for s in symbols_ if s not in model]
    pure = find_pure_symbol(symbols_, clauses, model)
    if pure is not None:
        s, v = pure
        return dpll(clauses, symbols_, {**model, s: v}, stats)
    unit = find_unit_clause(clauses, model)
    if unit is not None:
        s, v = unit
        return dpll(clauses, symbols_, {**model, s: v}, stats)
    P, rest = symbols_[0], symbols_[1:]
    r = dpll(clauses, rest, {**model, P: True}, stats)
    if r is not None:
        return r
    return dpll(clauses, rest, {**model, P: False}, stats)


def dpll_satisfiable(clauses):
    clauses = list(clauses)
    syms = sorted({lit_name(l) for c in clauses for l in c})
    stats = {'calls': 0}
    r = dpll(clauses, syms, {}, stats)
    return r is not None, stats['calls']


def tt_sat_clauses(clauses, limit=TT_LIMIT):
    syms = sorted({lit_name(l) for c in clauses for l in c})
    count = 0
    for m in all_models(syms):
        count += 1
        if count > limit:
            return None, count
        if all(clause_sat(c, m) for c in clauses):
            return True, count
    return False, count


def random_3sat(n, m, seed=1):
    random.seed(seed)
    clauses = []
    for _ in range(m):
        vs = random.sample(range(1, n + 1), 3)
        clauses.append(frozenset(
            f"x{v}" if random.random() < 0.5 else f"~x{v}" for v in vs
        ))
    return clauses


def equivalent(a, b):
    syms = sorted(symbols(a) | symbols(b))
    return all(pl_true(a, m) == pl_true(b, m) for m in all_models(syms))


def self_test():
    P, Q, R, A, B, C = (Sym(x) for x in "PQRABC")
    s = Imp(And(P, Q), R)
    assert symbols(s) == {'P', 'Q', 'R'}
    assert to_str(s) == "((P & Q) => R)"
    m1 = {'P': True, 'Q': False, 'R': True}
    assert pl_true(s, m1)
    assert not pl_true(Iff(P, Q), m1)
    assert not pl_true(Or(Not(P), Q), m1)
    assert tt_entails(And(P, Imp(P, Q)), Q)[0] is True
    assert tt_entails(Or(P, Q), P)[0] is False
    assert tt_entails(And(Not(Q), Imp(P, Q)), Not(P))[0] is True
    assert is_valid(Or(P, Not(P)))
    assert not is_satisfiable(And(P, Not(P)))
    assert equivalent(Not(And(P, Q)), Or(Not(P), Not(Q)))

    f = Iff(B, Or(A, C))
    assert to_clauses(to_cnf(f)) == {
        frozenset({'~B', 'A', 'C'}),
        frozenset({'~A', 'B'}),
        frozenset({'~C', 'B'}),
    }
    for g in [f, Not(And(P, Q)), Imp(P, Iff(Q, R)), Or(And(P, Q), Not(R))]:
        assert equivalent(g, to_cnf(g))

    assert resolve(frozenset({'A', 'B'}), frozenset({'~A', 'C'})) == [frozenset({'B', 'C'})]
    assert resolve(frozenset({'C'}), frozenset({'~C'})) == [frozenset()]
    kb = [frozenset({'A', 'B'}), frozenset({'~A', 'C'}), frozenset({'~B', 'C'})]
    assert pl_resolution(kb, C)[0] is True
    assert pl_resolution(kb, A)[0] is False

    sat_cls = [frozenset({'A'}), frozenset({'~A', 'B'}), frozenset({'~B', 'C'}),
               frozenset({'~C', 'D', 'E'}), frozenset({'~D', '~E'})]
    unsat_cls = [frozenset({'A', 'B'}), frozenset({'~A', 'B'}),
                 frozenset({'A', '~B'}), frozenset({'~A', '~B'})]
    assert dpll_satisfiable(sat_cls)[0] is True
    assert dpll_satisfiable(unsat_cls)[0] is False


def wumpus_kb():
    P11, P12, P21, P22, P31, B11, B21 = (
        Sym(x) for x in ["P11", "P12", "P21", "P22", "P31", "B11", "B21"]
    )
    rules = [
        Not(P11),
        Iff(B11, Or(P12, P21)),
        Iff(B21, Or(Or(P11, P22), P31)),
        Not(B11),
        B21,
    ]
    return reduce(And, rules)


def wumpus_queries():
    S = Sym
    return [
        ("¬P12", Not(S("P12"))),
        ("¬P21", Not(S("P21"))),
        ("¬P22", Not(S("P22"))),
        ("¬P31", Not(S("P31"))),
        ("P22 ∨ P31", Or(S("P22"), S("P31"))),
    ]


def check_entail(kb, alpha):
    tt, tt_cnt = tt_entails(kb, alpha)
    res, res_cnt = pl_resolution(to_clauses(to_cnf(kb)), alpha)
    sat, dp_cnt = dpll_satisfiable(to_clauses(to_cnf(And(kb, Not(alpha)))))
    return (tt, tt_cnt), (res, res_cnt), (not sat, dp_cnt)


def agree(vals):
    return len({v for v in vals if v is not None}) <= 1


def cell(ans, cnt):
    if ans is None:
        return f"хэт удаан ({cnt})"
    return str(cnt)


def main():
    self_test()

    kb = wumpus_kb()
    syms = sorted(symbols(kb))
    print("KB-г хангах загварын тоо:", sum(1 for m in all_models(syms) if pl_true(kb, m)))
    print()
    print(f"{'Асуулт':<12}{'TT':<8}{'Резолюц':<10}{'DPLL':<8}")
    for name, alpha in wumpus_queries():
        (t, _), (r, _), (d, _) = check_entail(kb, alpha)
        assert agree([t, r, d]), f"Аргууд зөрлөө: {name}"
        print(f"{name:<12}{str(t):<8}{str(r):<10}{str(d):<8}")

    print()
    header = f"{'Бодлого':<22}{'Хариу':<12}{'Үнэний хүснэгт':<24}{'Резолюц':<24}{'DPLL':<24}"
    print(header)
    print("-" * len(header))

    wumpus_targets = {"¬P12", "¬P22", "P22 ∨ P31"}
    for name, alpha in wumpus_queries():
        if name not in wumpus_targets:
            continue
        (t, tc), (r, rc), (d, dc) = check_entail(kb, alpha)
        assert agree([t, r, d])
        ans = t if t is not None else (r if r is not None else d)
        print(f"{'Wumpus: ' + name:<22}{str(ans):<12}{cell(t, tc):<24}{cell(r, rc):<24}{cell(d, dc):<24}")

    for n in (10, 15, 20):
        clauses = random_3sat(n, 4 * n, seed=1)
        (t, tc) = tt_sat_clauses(clauses)
        (u, uc) = refute(clauses)
        r = None if u is None else (not u)
        (d, dc) = dpll_satisfiable(clauses)
        assert agree([t, r, d]), f"3-SAT n={n} аргууд зөрлөө"
        ans = t if t is not None else (r if r is not None else d)
        label = f"3-SAT, n = {n}"
        print(f"{label:<22}{('SAT' if ans else 'UNSAT'):<12}{cell(t, tc):<24}{cell(r, uc):<24}{cell(d, dc):<24}")


if __name__ == "__main__":
    main()