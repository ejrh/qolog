import sys
import time

from term import *
from term_parser import parse, unparse

def bind(v, t):
    v.binding = t

def unbind_all(bound_vars):
    for v in bound_vars:
        v.binding = None

def unify_subterms(s1, s2):
    bound_vars = set()
    for t1, t2 in zip(s1, s2):
        result = unify(t1, t2)
        if result is None:
            unbind_all(bound_vars)
            return None
        bound_vars.update(result)
    return bound_vars

def unify(t1, t2):
    """
        Attempt to unify the two terms.  If they can be unified, variables in the terms may
        be bound; a set of newly-bound variables is returned.  If the terms cannot be unified,
        the variables are unchanged and None is returned.

        >>> db = Database()
        >>> unify_strs(db, 'x', 'y')
        >>> unify_strs(db, 'x', 'x')
        []
        >>> unify_strs(db, 'X', 'y')
        ['X']
        >>> unify_strs(db, 'X', 'Y')
        ['X']
        >>> unify_strs(db, 'X', 'X')
        []
        >>> unify_strs(db, 'X', 'f(a)')
        ['X']
        >>> unify_strs(db, 'f(X)', 'f(a)')
        ['X']
        >>> unify_strs(db, 'f(X, X)', 'f(a, b)')
        >>> unify_strs(db, 'f(X, Y)', 'f(a, b)')
        ['X', 'Y']
        >>> unify_strs(db, 'f(X, X)', 'f(a, a)')
        ['X']
        >>> unify_strs(db, '[X,Y]', 'Z')
        ['Z']
    """
    t1 = t1.resolve()
    t2 = t2.resolve()
    if same_atom(t1, t2) or same_variable(t1, t2) or same_integer(t1, t2):
        return set()
    elif isinstance(t1, Variable):
        bind(t1, t2)
        return {t1}
    elif isinstance(t2, Variable):
        bind(t2, t1)
        return {t2}
    elif same_functor(t1, t2):
        return unify_subterms(t1.subterms, t2.subterms)
    return None

def unify_strs(database, str1, str2):
    t1, t2, scope = parse(database.operators, str1, str2)
    unifications = unify(t1, t2)
    if unifications is None:
        return None
    return sorted(scope.var_mappings(unifications).keys())

def equals_rule(term, database):
    t1, t2 = term.subterms
    bound_vars = unify(t1, t2)
    if bound_vars is None:
        return
    yield bound_vars
    unbind_all(bound_vars)

def comma_rule(term, database):
    t1, t2 = term.subterms
    for bound_vars in prove(t1, database):
        for more_bound_vars in prove(t2, database):
            yield bound_vars.union(more_bound_vars)

def find_subgoals(term):
    subgoals = []
    def f(target):
        if target.is_functor(',', 2):
            for st in target.subterms:
                f(st)
        else:
            subgoals.append(target)
    f(term)
    return subgoals

def optimised_comma_rule(term, database):
    """
        An optimised comma rule that builds a list of subgoals from nested
        comma operators, and processes the list using a stack of generators,
        instead of recursively.
    """

    if not hasattr(term, 'subgoals'):
        term.subgoals = find_subgoals(term)

    generator_stack = []
    bound_vars_stack = []
    i = 0
    while i >= 0:
        if i == len(generator_stack):
            #print 'Create generator', i
            gen = prove(term.subgoals[i], database)
            generator_stack.append(gen)
            bound_vars_stack.append(None)
        try:
            bound_vars_stack[i] = generator_stack[i].next()
            i += 1
        except StopIteration:
            #print 'Discard generator', i
            generator_stack.pop()
            bound_vars_stack.pop()
            i -= 1
        if i >= len(term.subgoals):
            yield set.union(*bound_vars_stack)
            i -= 1

def semicolon_rule(term, database):
    t1, t2 = term.subterms
    for bound_vars in prove(t1, database, transmit_cut=True):
        yield bound_vars
    for bound_vars in prove(t2, database, transmit_cut=True):
        yield bound_vars

def true_rule(term, database):
    return [set()]

def fail_rule(term, database):
    return []

def not_rule(term, database):
    for bound_vars in prove(term.subterms[0], database):
        unbind_all(bound_vars)
        return []
    return [set()]

def assert_rule(term, database):
    rule = term.subterms[0]
    database.add_rule_at_end(rule)
    return [set()]

def retractall_rule(term, database):
    head = term.subterms[0]
    database.remove_matching_rules(head)
    return [set()]

def evaluate_term(term):
    term = term.resolve()
    if isinstance(term, Integer):
        return term.value
    elif isinstance(term, Variable):
        raise Exception('Argument not sufficiently instantiated')
    elif isinstance(term, Compound) and len(term.subterms) == 2:
        op = term.name
        lhs, rhs = term.subterms
        lhs_value = evaluate_term(lhs)
        rhs_value = evaluate_term(rhs)
        if op == '+':
            return lhs_value + rhs_value
        elif op == '-':
            return lhs_value - rhs_value
        elif op == '*':
            return lhs_value * rhs_value
        else:
            raise Exception('Unhandled operator: ' + op)
    else:
        raise Exception('Unhandled expression')

def is_rule(term, database):
    t1, t2 = term.subterms
    result = Integer(evaluate_term(t2))
    bound_vars = unify(t1, result)
    if bound_vars is None:
        return
    yield bound_vars
    unbind_all(bound_vars)

def arithmetic_comparison_rule(test):
    def f(term, database):
        t1, t2 = term.subterms
        result1 = evaluate_term(t1)
        result2 = evaluate_term(t2)
        if test(result1, result2):
            return [set()]
        return []
    return f

def display_rule(term, database):
    arg = term.subterms[0].resolve()
    print unparse(database.operators, arg, Scope()),
    return [set()]

def nl_rule(term, database):
    print
    return [set()]

def findall_rule(term, database):
    temp, goal, bag_var = term.subterms
    results = []
    for bound_vars in prove(goal, database):
        result = temp.copy_to_new_scope(Scope())
        results.append(result)
    bag = make_list(results)
    bound_vars = unify(bag_var, bag)
    if bound_vars is None:
        return
    yield bound_vars
    unbind_all(bound_vars)

def call_rule(term, database):
    return prove(term.subterms[0], database)

def once_rule(term, database):
    for bound_vars in prove(term.subterms[0], database):
        yield bound_vars
        unbind_all(bound_vars)
        return

def atmost_rule(term, database):
    num = term.subterms[0].resolve()
    if not isinstance(num, Integer):
        return
    i = 0
    for bound_vars in prove(term.subterms[1], database):
        yield bound_vars
        i += 1
        if i >= num.value:
            unbind_all(bound_vars)
            return

class CutBacktrack(Exception):
    pass

def cut_rule(term, database):
    """
        >>> db = Database()
        >>> prove_str('(X = 1; X = 2), !, Y is X + 1', db)
        X = 1, Y = 2
        >>> db.add_rules(['data(one)', 'data(two)', 'data(three)'])
        >>> db.add_rules(['cut_test_b(X) :- data(X), !', 'cut_test_b(last)'])
        >>> prove_str('cut_test_b(X)', db)
        X = one
        >>> prove_str('(X = 1, !; X = 2)', db)
        X = 1
    """
    yield set()
    raise CutBacktrack

def var_rule(term, database):
    term = term.subterms[0].resolve()
    if isinstance(term, Variable):
        return [set()]
    return []

def integer_rule(term, database):
    term = term.subterms[0].resolve()
    if isinstance(term, Integer):
        return [set()]
    return []

def between_rule(term, database):
    low, high, value = term.subterms
    low = low.resolve()
    high = high.resolve()
    if not isinstance(low, Integer) or not isinstance(high, Integer):
        return
    value = value.resolve()
    if isinstance(value, Integer):
        if low.value <= value.value <= high.value:
            yield set()
        return
    for i in range(low.value, high.value+1):
        bound_vars = unify(value, Integer(i))
        yield bound_vars
        unbind_all(bound_vars)

def compile_rule(rule_term):
    if not rule_term.is_functor(':-', 2):
        raise Exception('Invalid rule: %s' % rule_term)
    def f(term, database):
        local_scope = Scope()
        local_rule = rule_term.copy_to_new_scope(local_scope)
        head, body = local_rule.subterms
        bound_vars = unify(head, term)
        if bound_vars is None:
            return
        for more_bound_vars in prove(body, database):
            yield bound_vars.union(more_bound_vars)
        unbind_all(bound_vars)
    return f

class Database(object):
    def __init__(self):
        self.rule_index = {}
        self.operators = {}
        self.register_builtins()

    def register_builtins(self):
        self.register_operator('=', 700, 'xfx')
        self.register_operator(',', 1000, 'xfy')
        self.register_operator(';', 1100, 'xfy')
        self.register_operator(':-', 1200, 'xfx')
        self.register_operator('is', 700, 'xfx')
        self.register_operator('+', 500, 'yfx')
        self.register_operator('-', 500, 'yfx')
        self.register_operator('*', 400, 'yfx')
        self.register_operator('=:=', 700, 'xfx')
        self.register_operator('=\\=', 700, 'xfx')
        self.register_operator('>', 700, 'xfx')
        self.register_operator('>=', 700, 'xfx')
        self.register_operator('<', 700, 'xfx')
        self.register_operator('=<', 700, 'xfx')
        self.register_operator('\\+', 900, 'fy')

        self.register_at_end(('=', 2), '_ = _', equals_rule)
        #self.register_at_end((',', 2), '_ , _', comma_rule)
        #self.register_at_end((',', 2), '_ , _', optimised_comma_rule)
        self.register_at_end((';', 2), '_ ; _', semicolon_rule)
        self.register_at_end(('true', 0), 'true', true_rule)
        self.register_at_end(('fail', 0), 'fail', fail_rule)
        self.register_at_end(('\\+', 1), '\\+ _', not_rule)
        self.register_at_end(('assert', 1), 'assert(_)', assert_rule)
        self.register_at_end(('retractall', 1), 'retractall(_)', retractall_rule)
        self.register_at_end(('is', 2), '_ is _', is_rule)
        self.register_at_end(('=:=', 2), '_ =:= _', arithmetic_comparison_rule(lambda a,b: a == b))
        self.register_at_end(('=\\=', 2), '_ =\\= _', arithmetic_comparison_rule(lambda a,b: a != b))
        self.register_at_end(('>=', 2), '_ >= _', arithmetic_comparison_rule(lambda a,b: a >= b))
        self.register_at_end(('>', 2), '_ > _', arithmetic_comparison_rule(lambda a,b: a > b))
        self.register_at_end(('=<', 2), '_ =< _', arithmetic_comparison_rule(lambda a,b: a <= b))
        self.register_at_end(('<', 2), '_ < _', arithmetic_comparison_rule(lambda a,b: a < b))
        self.register_at_end(('display', 1), 'display(_)', display_rule)
        self.register_at_end(('nl', 0), 'nl', nl_rule)
        self.register_at_end(('findall', 3), 'findall(_, _, _)', findall_rule)
        self.register_at_end(('call', 1), 'call(_)', call_rule)
        self.register_at_end(('once', 1), 'once(_)', once_rule)
        self.register_at_end(('atmost', 2), 'atmost(_, _)', atmost_rule)
        self.register_at_end(('!', 0), '!', cut_rule)
        self.register_at_end(('var', 1), 'var(_)', var_rule)
        self.register_at_end(('integer', 1), 'integer(_)', integer_rule)
        self.register_at_end(('between', 3), 'between(_, _, _)', between_rule)

    def register_operator(self, name, precedence, typ):
        self.operators[name] = precedence, typ

    def register_block(self, functor, rule_pairs):
        if functor in self.rule_index:
            raise Exception('Cannot override existing rule for %s' % (functor,))
        self.rule_index[functor] = rule_pairs

    def register_at_end(self, functor, head, rule):
        if functor not in self.rule_index:
            self.rule_index[functor] = []
        self.rule_index[functor].append((head, rule))

    def check_and_compile_rule(self, rule):
        if type(rule) is str:
            rule, _ = parse(self.operators, rule)
        else:
            rule = rule.copy_to_new_scope(Scope())
        if not rule.is_functor(':-', 2):
            rule = Compound(':-', rule, Atom('true'))
            subgoals = []
        else:
            subgoals = find_subgoals(rule.subterms[1])
        head = rule.subterms[0]
        functor = head.get_functor()
        if functor is None:
            raise Exception('Cannot make a rule with head %s' % (head,))
        compiled_rule = compile_rule(rule)
        compiled_rule.subgoals = subgoals
        return functor, head, compiled_rule

    def add_rules(self, rules):
        functor_map = {}
        for rule in rules:
            functor, head, compiled_rule = self.check_and_compile_rule(rule)
            if functor not in functor_map:
                functor_map[functor] = []
            functor_map[functor].append((head, compiled_rule))

        for functor, rule_pairs in functor_map.items():
            self.register_block(functor, rule_pairs)

    def add_rule_at_end(self, rule):
        functor, head, compiled_rule = self.check_and_compile_rule(rule)
        self.register_at_end(functor, head, compiled_rule)

    def remove_matching_rules(self, head):
        functor = head.get_functor()
        if functor not in self.rule_index:
            return

        new_rulepairs = []
        for rule_head, rule in self.rule_index[functor]:
            bound_vars = unify(rule_head, head)
            if bound_vars is None:
                new_rulepairs.append((rule_head, rule))
            else:
                unbind_all(bound_vars)
                print 'retracted', rule_head
        self.rule_index[functor] = new_rulepairs

    def get_rules(self, functor):
        if functor not in self.rule_index:
            raise Exception('No rules for %s' % (functor,))
        return self.rule_index[functor]

class ListRules(object):
    """
        >>> db = Database()
        >>> db.add_rules(LIST_RULES)

        >>> prove_str('length([], 0)', db)
        <BLANKLINE>
        >>> prove_str('length([a], 1)', db)
        <BLANKLINE>
        >>> prove_str('length([a], 2)', db)
        >>> prove_str('length([a], X)', db)
        X = 1
        >>> prove_str('length([a,b,c], X)', db)
        X = 3
        >>> prove_str('length(L, 2)', db)
        L = [_G1,_G2]
        >>> prove_str('atmost(3, length(L, N))', db)
        L = [], N = 0
        L = [_G1], N = 1
        L = [_G1,_G2], N = 2

        >>> prove_str('member(X, [a,b,c]), Y = [X|Z], Y = [_,2]', db)
        X = a, Y = [a,2], Z = [2]
        X = b, Y = [b,2], Z = [2]
        X = c, Y = [c,2], Z = [2]

        >>> prove_str('reverse([a,b,c,d], X)', db)
        X = [d,c,b,a]

        >>> prove_str('concat([a,b,c], [d,e], Z)', db)
        Z = [a,b,c,d,e]
        >>> prove_str('concat(X, [y,z], [w,x,y,z])', db)
        X = [w,x]
    """

LIST_RULES = [
    'length([], 0)',
    'length([_|T], N) :- var(N), length_ct(T, 1, N)',
    'length([_|T], N) :- integer(N), Nm1 is N - 1, length_gen(T, Nm1)',
    'length_ct([], N, N)',
    'length_ct([_|T], N0, N) :- N1 is N0 + 1, length_ct(T, N1, N)',
    'length_gen([], 0)',
    'length_gen([_|T], N) :- N >= 0, Nm1 is N - 1, length_gen(T, Nm1)',
    'member(M, [M|_])',
    'member(M, L) :- L = [_|L2], member(M, L2)',
    'reverse(X, Y) :- reverse(X, [], Y, Y)',
    'reverse([], A, A, [])',
    'reverse([A|B], C, D, [_|E]) :- reverse(B, [A|C], D, E)',
    'concat([], B, B)',
    'concat([H|A], B, [H|C]) :- concat(A, B, C)',
]

ARITHMETIC_RULES = [
#    'between(L, H, V) :- integer(V), L =< V, V =< H',
#    'between(L, H, V) :- var(V), L =< H, V = L',
#    'between(L, H, V) :- var(V), L < H, Lp1 is L + 1, between(Lp1, H, V)',
]

def bound_vars_str(database, bound_vars, scope):
    return ', '.join('%s = %s' % (str(v), unparse(database.operators, t, scope)) for v,t in sorted(scope.var_mappings(bound_vars).items()))

BUILTIN = object()
DEFINITION = object()

def prove(goal, database, transmit_cut=False):
    """
        Attempt to prove a goal by unifying it with all possible rules.

        >>> db = Database()
        >>> db.add_rules(LIST_RULES)
        >>> prove_str('X = a; X = b', db)
        X = a
        X = b
        >>> prove_str('X = a; Y = b', db)
        X = a
        Y = b
        >>> prove_str('X = a, X = b', db)
        >>> prove_str('X = a, Y = b', db)
        X = a, Y = b
        >>> prove_str('X = Y, X = 5', db)
        X = 5, Y = 5
        >>> prove_str('X = Y, Y = 5', db)
        X = 5, Y = 5
        >>> prove_str('Y = 5, X is 3 + Y', db)
        X = 8, Y = 5
        >>> prove_str('X = Y', db)
        X = Y
        >>> prove_str('6 is 5', db)
        >>> prove_str('L1 = [c,d], L2 = [a,b], L2 = [a,L3]', db)
        L1 = [c,d], L2 = [a,b], L3 = b
        >>> prove_str('X = [a,b|Z], X = [A,B,c,d,e]', db)
        A = a, B = b, X = [a,b,c,d,e], Z = [c,d,e]
        >>> prove_str('X is 2 + 2', db)
        X = 4
        >>> prove_str("(display('X could be any of... '), member(X, [1,2,3]), display(X), fail); nl, fail", db)
        X could be any of...  1 2 3
        >>> prove_str('findall(X, member(X, [a,b,c]), S)', db)
        S = [a,b,c]
        >>> prove_str('X = (Y = 1), X', db)
        X = (1 = 1), Y = 1
        >>> prove_str('X', db)
        Traceback (most recent call last):
        Exception: No rules for unbound variable
        >>> prove_str('X = member(Z, [a,b]), call(X)', db)
        X = member(a, [a,b]), Z = a
        X = member(b, [a,b]), Z = b
        >>> prove_str('once(member(X, [1,2,3]))', db)
        X = 1
        >>> prove_str('once(member(4, [1,2,3]))', db)
        >>> prove_str('once(X = 1); var(X)', db)
        X = 1
        <BLANKLINE>
        >>> prove_str('G = (X = 1), once(G)', db)
        G = (1 = 1), X = 1
        >>> prove_str('atmost(2, (X = 1; Y = 2; Z = 3)', db)
        X = 1
        Y = 2
        >>> prove_str('X = 5, fail; X = 7', db)
        X = 7
        >>> prove_str('var(X), Y = 5', db)
        Y = 5
        >>> prove_str('X = 3, var(X), Y = 5', db)
        >>> prove_str('integer(3), Y = 1; integer(X), Y = 2; integer(w), Y = 3', db)
        Y = 1
        >>> prove_str('\+(X = 5)', db)
        >>> prove_str('\+(X = 5); X = 7', db)
        X = 7
        >>> prove_str('X = 3, \+(X = 5)', db)
        X = 3
        >>> db.add_rules(['triplicate(X, W) :- W = [X,X,X]'])
        >>> prove_str('X = 1, findall(S, triplicate(X, S), B)', db)
        B = [[1,1,1]], X = 1
        >>> prove_str('findall(S, triplicate(X, S), B), X = 1, B = [[2,2,2]]', db)
        B = [[2,2,2]], X = 1
        >>> prove_str('assert(human(socrates)), assert(human(pythagoras)), human(X)', db)
        X = socrates
        X = pythagoras
        >>> prove_str('''assert(divides(P, P) :- P > 0), \
                assert((divides(P, Q) :- P > 0, Q > P, QmP is Q - P, divides(P, QmP))), \
                assert(prime(P) :- known_prime(P)), \
                assert((prime(P) :- \+known_prime(P), \
                        findall(_, (between(2, P, D), known_prime(D), divides(D, P)), []), \
                        assert(known_prime(P)))), \
                assert(known_prime(2)), \
                findall(P, (between(2, 25, P), prime(P)), S)''', db)
        S = [2,3,5,7,11,13,17,19,23]

        ALGORITHM EXAMPLE

        We maintain two stacks, the "goal stack" and the "run stack".  They can be depicted as follows:

        Run stack (grows ->)                              Goal stack (grows <-)

        Goals to be proved are pushed to the goal stack.  For example, "a, b, c" (assume "b :- d" and "b :- e, f"):

        []                                                a   b   c

        We pop a goal off the goal stack, and look it up in the database.
          - If it's builtin, we create a builtin generator for it and push that to the run stack.
          - If it's a defined predicate, we create a definition generator for it and push that to the run stack.

        B(a)                                              b   c

        We fetch from the generator at the top of the run stack.
          - If it's a builtin generator, we pop the next goal and turn that into a generator as above.
          - If it's a definition generator, it will yield the next clause (rule or fact) for that predicate,
            with its head pre-unified with the goal.  We push all subgoals for that clause (0 for a fact) to the goal
            stack, keeping a note of the number of subgoals for the clause.

        For our example, when B(a) yielded a solution, we created a definition generator D(b).

        B(a)   D(b)                                       c

        D(b) then yielded the first clause "b :- d".

        B(a)   D(b)                                       d, c
               1 subgoal

        We pop the next goal "d" and turn that into a generator, fetch from it, and then pop the next goal "c".

        B(a)   D(b)         G(d)                          c
               1 subgoal

        B(a)   D(b)         G(d)   G(c)                   []
               1 subgoal

        Fetching from G(c) yields a solution.  As the goal stack is empty, we combine all the solutions from
        generators in the stack, and yield it.

        Then we fetch again from the generator at the top of the run stack, G(c).  G(c) does not have any more solutions,
        so we pop it off the run stack and put it back on the goal stack.

        B(a)   D(b)         G(d)                          c
               1 subgoal

        We fetch from G(d), it does not have any more solutions, so we do the same.

        B(a)   D(b)                                       d   c
               1 subgoal

        We fetch from the definition generator, D(b), and it yields the next clause "b :- e, f".  We pop the subgoals from
        the previous clause, and push the subgoals from this one.

        B(a)   D(b)                                       e    f   c
               2 subgoals

        We continue with the next goal on the goal stack, etc., yielding additional solutions.  Eventually D(b) has no
        more clauses to yield, so we pop the subgoals off, finally pop D(b), and return b to the goal stack.

        B(a)                                              b   c

        We fetch again from B(a).  If it yields again, we repeat the process with the next goal "b".  Otherwise,
        we pop it and push it back to the goal stack.

        []                                                a   b   c

        The run stack is now empty, and the algorithm terminates.

    """

    goal_stack = []
    run_stack = []
    subgoal_count_stack = []
    bound_vars_stack = []

    goal = goal.resolve()

    subgoals = find_subgoals(goal)
    for sg in reversed(subgoals):
        goal_stack.append(sg)

    def generate_clauses(goal, clauses):
        for head, subgoals in clauses:

            local_scope = Scope()
            local_head = head.copy_to_new_scope(local_scope)
            local_subgoals = [x.copy_to_new_scope(local_scope) for x in subgoals]

            bound_vars = unify(local_head, goal)
            if bound_vars is None:
                continue
            yield bound_vars, local_subgoals
            unbind_all(bound_vars)

    def pop_subgoals():
        subgoals_to_pop = subgoal_count_stack.pop()
        for i in range(subgoals_to_pop):
            goal_stack.pop()

    #print 'Proving goals: ', [unparse(database.operators, x, Scope()) for x in goal_stack]
    while True:

        if len(goal_stack) == 0:
            all_bound_vars = set.union(*bound_vars_stack)
            yield all_bound_vars
        else:
            next_goal = goal_stack.pop()
            next_goal = next_goal.resolve()
            if isinstance(next_goal, Variable):
                raise Exception('No rules for unbound variable')
            functor = next_goal.get_functor()
            rules = database.get_rules(functor)
            if len(rules) == 0:
                raise Exception('No rules for functor %s', functor)

            if (len(rules) == 1 and not hasattr(rules[0][1], 'subgoals')):
                builtin = rules[0][1]
                gen = iter(builtin(next_goal, database))
                run_stack.append((BUILTIN, next_goal, gen))
                #print 'Pushed builtin gen', len(run_stack)
            else:
                clauses = [(x[0], x[1].subgoals) for x in rules]
                gen = generate_clauses(next_goal, clauses)
                run_stack.append((DEFINITION, next_goal, gen))
                subgoal_count_stack.append(0)
                #print 'Pushed definition gen', len(run_stack)
            bound_vars_stack.append(set())

        while len(run_stack) > 0:
            try:
                bound_vars_stack.pop()
                typ, gen_goal, gen = run_stack[-1]
                result = gen.next()
                if typ is DEFINITION:
                    pop_subgoals()
                    new_bound_vars, subgoals = result
                    for sg in reversed(subgoals):
                        goal_stack.append(sg)
                    subgoal_count_stack.append(len(subgoals))
                    #print 'Pushed %d subgoals' % len(subgoals)
                elif typ is BUILTIN:
                    new_bound_vars = result
                else:
                    raise Exception
                bound_vars_stack.append(new_bound_vars)
                #print 'Fetched from gen', len(run_stack)
                break
            except StopIteration:
                typ, gen_goal, gen = run_stack.pop()
                #print 'Popped gen', len(run_stack)
                if typ is DEFINITION:
                    pop_subgoals()
                goal_stack.append(gen_goal)
            except CutBacktrack:
                # At this point, the cut is the top of the run stack.  We pop it and push it back to the goal stack.
                # We must then pop (and unbind from) generators until the cut has disappeared from the goal stack.
                typ, gen_goal, gen = run_stack.pop()
                goal_stack.append(gen_goal)
                goal_stack_len = len(goal_stack)
                while len(run_stack) > 0:
                    typ, gen_goal, gen = run_stack.pop()
                    bound_vars = bound_vars_stack.pop()
                    unbind_all(bound_vars)
                    if typ is DEFINITION:
                        pop_subgoals()
                    goal_stack.append(gen_goal)

                    if typ is DEFINITION and len(goal_stack) < goal_stack_len:
                        break

                # If we were called with transmit_cut (e.g. by semicolon_rule), and we've not yet encountered the
                # enclosing predicate of the cut, then we rethrow it to be handled by the caller.
                if transmit_cut and len(run_stack) == 0:
                    raise

        if len(run_stack) == 0:
            break

    #print 'Finished proving'

def prove_str(goal_str, database):
    goal, scope = parse(database.operators, goal_str)
    for bindings in prove(goal, database):
        print bound_vars_str(database, bindings, scope)

def prove_interactively(goal, scope, database):
    solution_num = 0
    for bound_vars in prove(goal, database):
        solution_num += 1
        print '%d.  %s' % (solution_num, bound_vars_str(database, bound_vars, scope))
        if solution_num >= 100:
            print '(too many solutions)'
            break
    print '(%d solutions)' % solution_num

def main():
    query_str = ' '.join(sys.argv[1:])
    if query_str == '':
        print 'Please enter a query on the command line (you might need quotes around it)'
        print 'E.g.   qolog.py   assert(prime(3)), assert(prime(5)), assert(prime(7)), findall(S, (prime(P), prime(Q), S is P*Q), B)'
        return
    db = Database()
    db.add_rules(LIST_RULES)
    db.add_rules(ARITHMETIC_RULES)
    goal, scope = parse(db.operators, query_str)
    print 'Proving:', unparse(db.operators, goal, scope)
    t0 = time.time()
    prove_interactively(goal, scope, db)
    print 'Ran for %0.2f seconds' % (time.time() - t0)

if __name__ == '__main__':
    main()
