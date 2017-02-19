import sys
import string

class Term(object):
    pass

class Atom(Term):
    def __init__(self, name):
        self.name = name

    def get_vars(self):
        return []

    def copy_to_new_scope(self, scope):
        return self

    def __repr__(self):
        return 'Atom(%s)' % repr(self.name)

    def __str__(self):
        return self.name

class Compound(Term):
    def __init__(self, name, subterms):
        self.name = name
        self.subterms = subterms

    def get_vars(self):
        vars = []
        for s in self.subterms:
            vars.extend(s.get_vars())
        return vars

    def copy_to_new_scope(self, scope):
        return Compound(self.name, [s.copy_to_new_scope(scope) for s in self.subterms])

    def __repr__(self):
        return 'Compound(%s, [%s])' % (repr(self.name), ', '.join(repr(x) for x in self.subterms))

    def __str__(self):
        return '%s(%s)' % (self.name, ', '.join('%s' % resolve_variable(x) for x in self.subterms))

class Variable(Term):
    def __init__(self, name):
        self.name = name
        self.binding = None

    def get_vars(self):
        return [self]

    def copy_to_new_scope(self, scope):
        return scope.var(self.name)

    def __repr__(self):
        return 'Variable(%s)' % (repr(self.name))

    def __str__(self):
        return self.name

class Integer(Term):
    def __init__(self, value):
        self.value = value

    def get_vars(self):
        return []

    def copy_to_new_scope(self, scope):
        return self

    def __repr__(self):
        return 'Integer(%s)' % repr(self.value)

    def __str__(self):
        return str(self.value)

class Scope(object):
    def __init__(self):
        self.vars = {}
        self.next_anonymous_id = 1

    def var(self, name):
        if name == '_':
            return Variable('_%d' % self.get_anonymous_id())
        if name not in self.vars:
            self.vars[name] = Variable(name)
        return self.vars[name]

    def get_anonymous_id(self):
        rv = self.next_anonymous_id
        self.next_anonymous_id += 1
        return rv

LIST_NIL = '[]'
LIST_CONS = '[|]'

def make_list(parts, tail=None):
    """
        Construct a list term out of a Python list of terms, and an optional tail.

        >>> make_list([])
        Atom('[]')
        >>> make_list([Atom('hello')])
        Compound('[|]', [Atom('hello'), Atom('[]')])
        >>> make_list([], Atom('[]'))
        Atom('[]')
        >>> make_list([], Compound('[|]', [Atom('hello'), Atom('[]')]))
        Compound('[|]', [Atom('hello'), Atom('[]')])
    """
    if tail is None:
        lst = Atom(LIST_NIL)
    else:
        lst = tail
    for p in reversed(parts):
        lst = Compound(LIST_CONS, [p, lst])
    return lst

ATOM_CHARS = string.ascii_lowercase + '\''
WORD_CHARS = string.letters + string.digits + '_'
OPERATOR_CHARS = ',=:-'
SIMPLE_CHARS = WORD_CHARS + '(['

class Tokeniser(object):
    def __init__(self, term_str):
        self.term_str = term_str
        #print >>sys.stderr, '[[%s]]' % term_str
        self.pos = 0
        self.cached = None

    def peek(self):
        if self.cached is None:
            self.cached = self.do_next()
        return self.cached

    def next(self):
        token = self.do_next()
        #print >>sys.stderr, '[%s]' % token
        return token

    def do_next(self):
        if self.cached is not None:
            rv = self.cached
            self.cached = None
            return rv

        self.skip_whitespace()

        if self.peek_ch() is None:
            return None

        if self.peek_ch() == '\'':
            self.pos += 1
            start_pos = self.pos
            x = self.peek_ch()
            while x is not None and x != '\'':
                self.pos += 1
                x = self.peek_ch()
            word = self.term_str[start_pos:self.pos]
            self.pos += 1
            return word
        elif self.peek_ch() in WORD_CHARS:
            start_pos = self.pos
            x = self.peek_ch()
            while x is not None and x in WORD_CHARS:
                self.pos += 1
                x = self.peek_ch()
            word = self.term_str[start_pos:self.pos]
            return word
        elif self.peek_ch() in OPERATOR_CHARS:
            start_pos = self.pos
            x = self.peek_ch()
            while x is not None and x in OPERATOR_CHARS:
                self.pos += 1
                x = self.peek_ch()
            word = self.term_str[start_pos:self.pos]
            return word
        else:
            return self.get_ch()

    def get_ch(self):
        if self.pos < len(self.term_str):
            ch = self.term_str[self.pos]
            self.pos += 1
            return ch
        else:
            return None

    def peek_ch(self):
        if self.pos < len(self.term_str):
            return self.term_str[self.pos]
        else:
            return None

    def skip_whitespace(self):
        while self.pos < len(self.term_str) and self.term_str[self.pos] in string.whitespace:
            self.pos += 1

def tokenise_str(input_str):
    """
        >>> tokenise_str('X = 5')
        ['X', '=', '5']
        >>> tokenise_str("'hello there'")
        ['hello there']
    """
    t = Tokeniser(input_str)
    tokens = []
    while True:
        token = t.next()
        if token is None:
            break
        tokens.append(token)
    return tokens


OPERATORS = {
    '=': (700, 'xfx'),
    ',': (1000, 'xfy'),
    ';': (1100, 'xfy'),
    ':-': (1200, 'xfx'),
    'is': (700, 'xfx'),
    '+': (500, 'yfx'),
}

class Parser(object):
    def __init__(self, term_str):
        self.tokeniser = Tokeniser(term_str)
        self.scope = Scope()

    def reset(self, term_str):
        self.tokeniser = Tokeniser(term_str)

    def parse(self, terminators=''):
        value_stack = []
        operator_stack = []

        def reduce():
            stack_oper = operator_stack.pop()
            v2 = value_stack.pop()
            v1 = value_stack.pop()
            item = Compound(stack_oper, [v1, v2])
            value_stack.append(item)
            #print>>sys.stderr, 'reduced using operator', stack_oper

        while self.tokeniser.peek() is not None and self.tokeniser.peek() not in terminators:
            next_tok = self.tokeniser.peek()
            if next_tok not in OPERATORS:
                item = self.parse_simple()
                value_stack.append(item)
                #print>>sys.stderr, 'push value', item
                continue

            operator = self.tokeniser.next()
            prec, type = OPERATORS[operator]
            while len(operator_stack) > 0:
                stack_oper = operator_stack[-1]
                stack_prec, stack_type = OPERATORS[stack_oper]
                if stack_prec < prec:
                    reduce()
                else:
                    break
            operator_stack.append(operator)
            #print>>sys.stderr, 'push operator', operator

        while len(operator_stack) > 0:
            reduce()

        #print >>sys.stderr, value_stack
        #print >>sys.stderr, operator_stack

        if operator_stack:
            raise Exception('Unused operators: %s' % operator_stack)

        if len(value_stack) != 1:
            raise Exception('Unreduced value stack: %s' % value_stack)

        return value_stack[0]

    def parse_simple(self):
        tok = self.tokeniser.next()
        if tok[0] in ATOM_CHARS:
            term = self.parse_atom_or_compound(tok)
        elif tok[0] in string.ascii_uppercase or tok[0] == '_':
            term = self.parse_variable(tok)
        elif tok[0] in string.digits:
            term = Integer(int(tok))
        elif tok[0] == '(':
            term = self.parse(')')
            self.tokeniser.next()
        elif tok[0] == '[':
            term = self.parse_list()
            self.tokeniser.next()
        else:
            raise Exception('Unhandled token %s' % repr(tok))

        return term

    def parse_list(self):
        parts = []
        if self.tokeniser.peek() == ']':
            return make_list(parts)

        term = self.parse(',|]')
        parts.append(term)

        while self.tokeniser.peek() == ',':
            self.tokeniser.next()
            term = self.parse(',|]')
            parts.append(term)
        if self.tokeniser.peek() == '|':
            self.tokeniser.next()
            tail = self.parse(']')
        else:
            tail = None
        return make_list(parts, tail)

    def parse_variable(self, name):
        return self.scope.var(name)

    def parse_atom_or_compound(self, name):
        if self.tokeniser.peek() == '(':
            subterms = []
            self.tokeniser.next()
            subterms.append(self.parse(',)'))
            while self.tokeniser.peek() == ',':
                self.tokeniser.next()
                subterms.append(self.parse(',)'))
            self.tokeniser.next()
            return Compound(name, subterms)
        else:
            return Atom(name)

def parse(term_str, other_term_str=None):
    """
        Parse a Prolog term string into a Term object.

        >>> parse('x')
        Atom('x')
        >>> parse("'hello there'")
        Atom('hello there')
        >>> parse('X')
        Variable('X')
        >>> parse('_X')
        Variable('_X')
        >>> parse('1')
        Integer(1)
        >>> parse('(x)')
        Atom('x')
        >>> parse('f(a)')
        Compound('f', [Atom('a')])
        >>> parse('[]')
        Atom('[]')
        >>> parse('X = a; X = b')
        Compound(';', [Compound('=', [Variable('X'), Atom('a')]), Compound('=', [Variable('X'), Atom('b')])])
        >>> parse('[a]')
        Compound('[|]', [Atom('a'), Atom('[]')])
        >>> parse('[a|X]')
        Compound('[|]', [Atom('a'), Variable('X')])
        >>> parse('f(a, 5)')
        Compound('f', [Atom('a'), Integer(5)])
        >>> parse('X = 4')
        Compound('=', [Variable('X'), Integer(4)])
        >>> parse('(X = 4), f(X)')
        Compound(',', [Compound('=', [Variable('X'), Integer(4)]), Compound('f', [Variable('X')])])
        >>> parse('X = 4, g')
        Compound(',', [Compound('=', [Variable('X'), Integer(4)]), Atom('g')])
        >>> parse('[X,Y]')
        Compound('[|]', [Variable('X'), Compound('[|]', [Variable('Y'), Atom('[]')])])
        >>> parse('X is Y+2')
        Compound('is', [Variable('X'), Compound('+', [Variable('Y'), Integer(2)])])
    """
    p = Parser(term_str)
    term = p.parse()
    if other_term_str is None:
        return term
    p.reset(other_term_str)
    other_term = p.parse()
    return term, other_term

def unparse(term):
    term = resolve_variable(term)
    if term_is_atom(term, LIST_NIL):
        return '[]'
    elif term_is_functor(term, LIST_CONS, 2):
        parts = []
        n = term
        while term_is_functor(n, LIST_CONS, 2):
            parts.append(n.subterms[0])
            n = resolve_variable(n.subterms[1])
        tail = n
        if term_is_atom(tail, LIST_NIL):
            return '[%s]' % ','.join(str(resolve_variable(p)) for p in parts)
        else:
            return '[%s|%s]' % (','.join(str(resolve_variable(p)) for p in parts), str(tail))
    elif term_is_operator(term):
        prec, type = OPERATORS[term.name]
        lhs, rhs = term.subterms
        return '%s %s %s' % (unparse(lhs), term.name, unparse(rhs))
    elif isinstance(term, Compound):
        return '%s(%s)' % (term.name, ', '.join('%s' % unparse(x) for x in term.subterms))
    else:
        return str(term)

def resolve_variable(v):
    if not isinstance(v, Variable):
        return v
    if v.binding is None:
        return v
    else:
        return resolve_variable(v.binding)

def term_equality(t1, t2, type, test):
    if not isinstance(t1, type):
        return False
    if not isinstance(t2, type):
        return False
    return test(t1, t2)

def same_atom(t1, t2):
    return term_equality(t1, t2, Atom, lambda a, b: a.name == b.name)

def same_variable(t1, t2):
    return term_equality(t1, t2, Variable, lambda a, b: a == b)

def same_integer(t1, t2):
    return term_equality(t1, t2, Integer, lambda a, b: a.value == b.value)

def same_functor(t1, t2):
    return term_equality(t1, t2, Compound, lambda a, b: a.name == b.name and len(a.subterms) == len(b.subterms))

def term_is_atom(term, name):
    if not isinstance(term, Atom):
        return False
    return term.name == name

def term_is_functor(term, name, arity):
    if not isinstance(term, Compound):
        return False
    return term.name == name and len(term.subterms) == arity

def term_is_operator(term):
    if not isinstance(term, Compound):
        return False
    return term.name in OPERATORS

def bind(v, t):
    v.binding = t

def unbind_all(bound_vars):
    for v in bound_vars:
        v.binding = None

def map_bound_vars(bound_vars, term):
    vars = set(term.get_vars())
    return set([v for v in vars if v.binding is not None])

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

        >>> unify_strs('x', 'y')
        >>> unify_strs('x', 'x')
        {}
        >>> unify_strs('X', 'y')
        {'X': 'y'}
        >>> unify_strs('X', 'Y')
        {'X': 'Y'}
        >>> unify_strs('X', 'X')
        {}
        >>> unify_strs('X', 'f(a)')
        {'X': 'f(a)'}
        >>> unify_strs('f(X)', 'f(a)')
        {'X': 'a'}
        >>> unify_strs('f(X, X)', 'f(a, b)')
        >>> unify_strs('f(X, X)', 'f(a, a)')
        {'X': 'a'}
        >>> unify_strs('[X,Y]', 'Z')
        {'Z': '[X,Y]'}
    """
    t1 = resolve_variable(t1)
    t2 = resolve_variable(t2)
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

def unify_strs(str1, str2):
    t1, t2 = parse(str1, str2)
    unifications = unify(t1, t2)
    if unifications is None:
        return None
    unification_strs = {}
    for v in unifications:
        unification_strs[str(v)] = unparse(v.binding)
    return unification_strs

def equals_rule(term):
    if not term_is_functor(term, '=', 2):
        return
    t1, t2 = term.subterms
    bound_vars = unify(t1, t2)
    if bound_vars is None:
        return
    yield bound_vars
    unbind_all(bound_vars)

def comma_rule(term):
    if not term_is_functor(term, ',', 2):
        return
    t1, t2 = term.subterms
    for bound_vars in prove(t1):
        for more_bound_vars in prove(t2):
            yield bound_vars.union(more_bound_vars)

def semicolon_rule(term):
    if not term_is_functor(term, ';', 2):
        return
    t1, t2 = term.subterms
    for bound_vars in prove(t1):
        yield bound_vars
    for bound_vars in prove(t2):
        yield bound_vars

def true_rule(term):
    if not term_is_atom(term, 'true'):
        return
    yield set()

def evaluate_term(term):
    #print >>sys.stderr, 'evaluating: %s' % unparse(term)
    term = resolve_variable(term)
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
    else:
        raise Exception('Unhandled expression')

def is_rule(term):
    if not term_is_functor(term, 'is', 2):
        return
    t1, t2 = term.subterms
    result = Integer(evaluate_term(t2))
    bound_vars = unify(t1, result)
    if bound_vars is None:
        return
    yield bound_vars
    unbind_all(bound_vars)

def write_rule(term):
    if not term_is_functor(term, 'write', 1):
        return
    arg = resolve_variable(term.subterms[0])
    print arg,
    yield set()

def nl_rule(term):
    if not term_is_atom(term, 'nl'):
        return
    print
    yield set()

def compile_rule(rule_str):
    rule_term = parse(rule_str)
    if not term_is_functor(rule_term, ':-', 2):
        raise Exception('Invalid rule: %s' % rule_term)
    def f(term):
        local_scope = Scope()
        local_rule = rule_term.copy_to_new_scope(local_scope)
        head, body = local_rule.subterms
        bound_vars = unify(term, head)
        if bound_vars is None:
            return
        for more_bound_vars in prove(body):
            yield map_bound_vars(bound_vars.union(more_bound_vars), term)
        unbind_all(bound_vars)
    return f

RULES = [
    equals_rule,
    comma_rule,
    semicolon_rule,
    true_rule,
    is_rule,
    write_rule,
    nl_rule,
    compile_rule('length([], 0) :- true'),
    compile_rule('length([_|T], X) :- length(T, X0), X is X0 + 1'),
    compile_rule('member(M, L) :- L = [M|L2]'),
    compile_rule('member(M, L) :- L = [X|L2], member(M, L2)'),
    compile_rule('reverse(X, Y) :- reverse(X, [], Y, Y)'),
    compile_rule('reverse([], A, A, []) :- true'),
    compile_rule('reverse([A|B], C, D, [_|E]) :- reverse(B, [A|C], D, E)'),
]

def bound_vars_str(vars):
    return ', '.join('%s = %s' % (str(v), unparse(v.binding)) for v in sorted(vars, key=lambda vv: vv.name))

def prove(goal):
    """
        Attempt to pove a goal by unifying it with all possible rules.

        >>> prove_str('X = a; X = b')
        X = a
        X = b
        >>> prove_str('X = a; Y = b')
        X = a
        Y = b
        >>> prove_str('X = a, X = b')
        >>> prove_str('X = a, Y = b')
        X = a, Y = b
        >>> prove_str('X = Y, X = 5')
        X = 5, Y = 5
        >>> prove_str('X = Y, Y = 5')
        X = 5, Y = 5
        >>> prove_str('Y = 5, X is 3 + Y')
        X = 8, Y = 5
        >>> prove_str('6 is 5')
        >>> prove_str('length([], 0)')
        <BLANKLINE>
        >>> prove_str('length([a], 1)')
        <BLANKLINE>
        >>> prove_str('length([a], 2)')
        >>> prove_str('length([a], X)')
        X = 1
        >>> prove_str('L1 = [c,d], L2 = [a,b], L2 = [a,L3]')
        L1 = [c,d], L2 = [a,b], L3 = b
        >>> prove_str('member(X, [a,b,c]), Y = [X|Z], Y = [W,2]')
        W = a, X = a, Y = [a,2], Z = [2]
        W = b, X = b, Y = [b,2], Z = [2]
        W = c, X = c, Y = [c,2], Z = [2]
        >>> prove_str('X = [a,b|Z], X = [A,B,c,d,e]')
        A = a, B = b, X = [a,b,c,d,e], Z = [c,d,e]
        >>> prove_str('reverse([a,b,c,d], X)')
        X = [d,c,b,a]
        >>> prove_str('X is 2 + 2')
        X = 4
        >>> prove_str("(write('X could be any of... '), member(X, [1,2,3]), write(X), fail); nl, fail")
        X could be any of...  1 2 3
        >>> prove_str('length([a,b,c], X)')
        X = 3

    """
    #print >>sys.stderr, "proving...", unparse(goal)
    for r in RULES:
        for bound_vars in r(goal):
            yield bound_vars

def prove_str(goal_str):
    goal = parse(goal_str)
    for bindings in prove(goal):
        print bound_vars_str(bindings)

def prove_interactively(goal):
    solution_num = 0
    for bound_vars in prove(goal):
        solution_num += 1
        print '%d.  %s' % (solution_num, bound_vars_str(bound_vars))
    print '(%d solutions)' % solution_num

def main():
    goal = parse('hello')
    print 'Proving:', unparse(goal)
    prove_interactively(goal)
    print

if __name__ == '__main__':
    main()
