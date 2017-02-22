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
    def __init__(self):
        self.binding = None

    def get_vars(self):
        return [self]

    def copy_to_new_scope(self, scope):
        term = resolve_variable(self)
        if isinstance(term, Variable):
            return scope.var(id(term))
        else:
            return term.copy_to_new_scope(scope)

    def __repr__(self):
        return 'Variable()'

    def __str__(self):
        return '_'

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
        self.names_to_vars = {}
        self.vars_to_names = {}
        self.next_id = 1

    def var(self, name):
        if name == '_':
            return Variable()
        if name not in self.names_to_vars:
            var = Variable()
            self.names_to_vars[name] = var
            self.vars_to_names[var] = name
            return var
        return self.names_to_vars[name]

    def var_mappings(self, vars):
        result = {}
        for name,var in self.names_to_vars.items():
            term = resolve_variable(var)
            if term == var:
                continue
            result[name] = term
        return result

    def get_name(self, var):
        if var in self.vars_to_names:
            return self.vars_to_names[var]
        else:
            name = '_G%d' % self.next_id
            self.next_id += 1
            self.vars_to_names[var] = name
            return name

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
OPERATOR_CHARS = ',=:->\\+'
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
            return "'%s'" % word
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
        Tokenise a Prolog term string into a list of individual tokens.

        >>> tokenise_str('X = 5')
        ['X', '=', '5']
        >>> tokenise_str("'hello there'")
        ["'hello there'"]
        >>> tokenise_str('\+foo(X)')
        ['\\\+', 'foo', '(', 'X', ')']
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
    '-': (500, 'yfx'),
    '>=': (700, 'xfx'),
    '\\+': (900, 'fy'),
}

class Parser(object):
    def __init__(self, term_str, scope):
        self.tokeniser = Tokeniser(term_str)
        self.scope = scope

    def reset(self, term_str):
        self.tokeniser = Tokeniser(term_str)

    def parse(self, terminators=''):
        value_stack = []
        operator_stack = []

        def reduce():
            stack_oper = operator_stack.pop()
            _, type = OPERATORS[stack_oper]
            if type in ('xfx', 'xfy', 'yfx'):
                v2 = value_stack.pop()
                v1 = value_stack.pop()
                item = Compound(stack_oper, [v1, v2])
            elif type in ('fx', 'xf', 'fy', 'yf'):
                v1 = value_stack.pop()
                item = Compound(stack_oper, [v1])
            else:
                raise Exception('Unhandled operator type ' + type)
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
            if name[0] == "'":
                name = name[1:]
            if name[-1] == "'":
                name = name[:-1]
            return Atom(name)

def parse(*term_strs):
    """
        Parse a Prolog term string into a Term object.

        >>> parse('x')[0]
        Atom('x')
        >>> parse("'hello there'")[0]
        Atom('hello there')
        >>> parse('X')[0]
        Variable()
        >>> parse('_X')[0]
        Variable()
        >>> parse('1')[0]
        Integer(1)
        >>> parse('(x)')[0]
        Atom('x')
        >>> parse('f(a)')[0]
        Compound('f', [Atom('a')])
        >>> parse('[]')[0]
        Atom('[]')
        >>> parse('X = a; X = b')[0]
        Compound(';', [Compound('=', [Variable(), Atom('a')]), Compound('=', [Variable(), Atom('b')])])
        >>> parse('[a]')[0]
        Compound('[|]', [Atom('a'), Atom('[]')])
        >>> parse('[a|X]')[0]
        Compound('[|]', [Atom('a'), Variable()])
        >>> parse('f(a, 5)')[0]
        Compound('f', [Atom('a'), Integer(5)])
        >>> parse('X = 4')[0]
        Compound('=', [Variable(), Integer(4)])
        >>> parse('(X = 4), f(X)')[0]
        Compound(',', [Compound('=', [Variable(), Integer(4)]), Compound('f', [Variable()])])
        >>> parse('X = 4, g')[0]
        Compound(',', [Compound('=', [Variable(), Integer(4)]), Atom('g')])
        >>> parse('[X,Y]')[0]
        Compound('[|]', [Variable(), Compound('[|]', [Variable(), Atom('[]')])])
        >>> parse('X is Y+2')[0]
        Compound('is', [Variable(), Compound('+', [Variable(), Integer(2)])])
        >>> parse('\+X')[0]
        Compound('\\\+', [Variable()])
        >>> parse('W , \+ X')[0]
        Compound(',', [Variable(), Compound('\\\+', [Variable()])])
        >>> parse('\+ X, W')[0]
        Compound(',', [Compound('\\\+', [Variable()]), Variable()])
        >>> parse('\+ X + W')[0]
        Compound('\\\+', [Compound('+', [Variable(), Variable()])])
    """
    scope = Scope()
    rvs = []
    for ts in term_strs:
        p = Parser(ts, scope)
        term = p.parse()
        rvs.append(term)
    rvs.append(scope)
    return tuple(rvs)

def unparse(term, scope):
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
            return '[%s]' % ','.join(unparse(p, scope) for p in parts)
        else:
            return '[%s|%s]' % (','.join(unparse(p, scope) for p in parts), unparse(tail, scope))
    elif term_is_operator(term):
        prec, type = OPERATORS[term.name]
        lhs, rhs = term.subterms
        return '%s %s %s' % (unparse(lhs, scope), term.name, unparse(rhs, scope))
    elif isinstance(term, Compound):
        return '%s(%s)' % (term.name, ', '.join('%s' % unparse(x, scope) for x in term.subterms))
    elif isinstance(term, Variable):
        return scope.get_name(term)
    elif isinstance(term, Integer):
        return str(term.value)
    elif isinstance(term, Atom):
        return term.name
    else:
        return '???'

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

def get_functor(term):
    if isinstance(term, Compound):
        return term.name, len(term.subterms)
    elif isinstance(term, Atom):
        return term.name, 0
    else:
        return None

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
        []
        >>> unify_strs('X', 'y')
        ['X']
        >>> unify_strs('X', 'Y')
        ['X']
        >>> unify_strs('X', 'X')
        []
        >>> unify_strs('X', 'f(a)')
        ['X']
        >>> unify_strs('f(X)', 'f(a)')
        ['X']
        >>> unify_strs('f(X, X)', 'f(a, b)')
        >>> unify_strs('f(X, Y)', 'f(a, b)')
        ['X', 'Y']
        >>> unify_strs('f(X, X)', 'f(a, a)')
        ['X']
        >>> unify_strs('[X,Y]', 'Z')
        ['Z']
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
    t1, t2, scope = parse(str1, str2)
    unifications = unify(t1, t2)
    if unifications is None:
        return None
    return sorted(scope.var_mappings(unifications).keys())

def equals_rule(term, database):
    if not term_is_functor(term, '=', 2):
        return
    t1, t2 = term.subterms
    bound_vars = unify(t1, t2)
    if bound_vars is None:
        return
    yield bound_vars
    unbind_all(bound_vars)

def comma_rule(term, database):
    if not term_is_functor(term, ',', 2):
        return
    t1, t2 = term.subterms
    for bound_vars in prove(t1, database):
        for more_bound_vars in prove(t2, database):
            yield bound_vars.union(more_bound_vars)

def semicolon_rule(term, database):
    if not term_is_functor(term, ';', 2):
        return
    t1, t2 = term.subterms
    for bound_vars in prove(t1, database):
        yield bound_vars
    for bound_vars in prove(t2, database):
        yield bound_vars

def true_rule(term, database):
    if not term_is_atom(term, 'true'):
        return []
    return [set()]

def fail_rule(term, database):
    if not term_is_atom(term, 'fail'):
        return []
    return []

def not_rule(term, database):
    if not term_is_functor(term, '\\+', 1):
        return []
    goal = term.subterms[0]
    passed = False
    bound_vars = None
    for bound_vars in prove(goal, database):
        passed = True
        break
    if bound_vars is not None:
        unbind_all(bound_vars)
    if passed:
        return []
    else:
        return [set()]

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
        elif op == '-':
            return lhs_value - rhs_value
        else:
            raise Exception('Unhandled operator: ' + op)
    else:
        raise Exception('Unhandled expression')

def is_rule(term, database):
    if not term_is_functor(term, 'is', 2):
        return
    t1, t2 = term.subterms
    result = Integer(evaluate_term(t2))
    bound_vars = unify(t1, result)
    if bound_vars is None:
        return
    yield bound_vars
    unbind_all(bound_vars)

def ge_rule(term, database):
    if not term_is_functor(term, '>=', 2):
        return []
    t1, t2 = term.subterms
    result1 = evaluate_term(t1)
    result2 = evaluate_term(t2)
    if result1 >= result2:
        return [set()]
    return []

def display_rule(term, database):
    if not term_is_functor(term, 'display', 1):
        return []
    arg = resolve_variable(term.subterms[0])
    print arg,
    return [set()]

def nl_rule(term, database):
    if not term_is_atom(term, 'nl'):
        return []
    print
    return [set()]

def findall_rule(term, database):
    if not term_is_functor(term, 'findall', 3):
        return
    temp, goal, bag_var = term.subterms
    results = []
    for bound_vars in prove(goal, database):
        result = temp.copy_to_new_scope(Scope())
        results.append(result)
    #print >>sys.stderr, 'results', results
    bag = make_list(results)
    unify(bag_var, bag)
    bound_vars = {bag_var}
    yield bound_vars
    unbind_all(bound_vars)

def var_rule(term, database):
    if not term_is_functor(term, 'var', 1):
        return []
    term = resolve_variable(term.subterms[0])
    if isinstance(term, Variable):
        return [set()]
    return []

def integer_rule(term, database):
    if not term_is_functor(term, 'integer', 1):
        return []
    term = resolve_variable(term.subterms[0])
    if isinstance(term, Integer):
        return [set()]
    return []

def compile_rule(rule_term):
    if not term_is_functor(rule_term, ':-', 2):
        raise Exception('Invalid rule: %s' % rule_term)
    def f(term, database):
        local_scope = Scope()
        local_rule = rule_term.copy_to_new_scope(local_scope)
        head, body = local_rule.subterms
        bound_vars = unify(head, term)
        if bound_vars is None:
            return
        for more_bound_vars in prove(body, database):
            yield map_bound_vars(bound_vars.union(more_bound_vars), term)
        unbind_all(bound_vars)
    return f

class Database(object):
    def __init__(self):
        self.rule_index = {}
        self.register_builtins()

    def register_builtins(self):
        self.register(('=', 2), equals_rule)
        self.register((',', 2), comma_rule)
        self.register((';', 2), semicolon_rule)
        self.register(('true', 0), true_rule)
        self.register(('fail', 0), fail_rule)
        self.register(('\\+', 1), not_rule)
        self.register(('is', 2), is_rule)
        self.register(('>=', 2), ge_rule)
        self.register(('display', 1), display_rule)
        self.register(('nl', 0), nl_rule)
        self.register(('findall', 3), findall_rule)
        self.register(('var', 1), var_rule)
        self.register(('integer', 1), integer_rule)

    def register(self, functor, rules):
        if functor in self.rule_index:
            raise Exception('Cannot override existing rule for %s' % (functor,))
        if type(rules) is not list:
            rules = [rules]
        self.rule_index[functor] = rules

    def add_rules(self, rules):
        functor_map = {}
        for rule in rules:
            if str(rule):
                rule, scope = parse(rule)
            if not term_is_functor(rule, ':-', 2):
                rule = Compound(':-', [rule, Atom('true')])
            head = rule.subterms[0]
            functor = get_functor(head)
            if functor is None:
                raise Exception('Cannot make a rule with head %s' % (head,))
            compiled_rule = compile_rule(rule)
            if functor not in functor_map:
                functor_map[functor] = []
            functor_map[functor].append(compiled_rule)

        for functor, rules in functor_map.items():
            self.register(functor, rules)

    def get_rules(self, functor):
        if functor not in self.rule_index:
            raise Exception('No rules for %s' % (functor,))
        return self.rule_index[functor]

LIST_RULES = [
    'length([], 0) :- true',
    'length([_|T], X) :- var(X), length(T, X0), X is X0 + 1',
    'length([_|T], X) :- integer(X), X >= 0, Xm1 is X - 1, length(T, Xm1)',
    'member(M, L) :- L = [M|L2]',
    'member(M, L) :- L = [X|L2], member(M, L2)',
    'reverse(X, Y) :- reverse(X, [], Y, Y)',
    'reverse([], A, A, []) :- true',
    'reverse([A|B], C, D, [_|E]) :- reverse(B, [A|C], D, E)',
    'concat([], B, B) :- true',
    'concat([H|A], B, [H|C]) :- concat(A, B, C)',
]

def bound_vars_str(vars, scope):
    return ', '.join('%s = %s' % (str(v), unparse(t, scope)) for v,t in sorted(scope.var_mappings(vars).items()))

def prove(goal, database):
    """
        Attempt to pove a goal by unifying it with all possible rules.

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
        >>> prove_str('length([], 0)', db)
        <BLANKLINE>
        >>> prove_str('length([a], 1)', db)
        <BLANKLINE>
        >>> prove_str('length([a], 2)', db)
        >>> prove_str('length([a], X)', db)
        X = 1
        >>> prove_str('L1 = [c,d], L2 = [a,b], L2 = [a,L3]', db)
        L1 = [c,d], L2 = [a,b], L3 = b
        >>> prove_str('member(X, [a,b,c]), Y = [X|Z], Y = [W,2]', db)
        W = a, X = a, Y = [a,2], Z = [2]
        W = b, X = b, Y = [b,2], Z = [2]
        W = c, X = c, Y = [c,2], Z = [2]
        >>> prove_str('X = [a,b|Z], X = [A,B,c,d,e]', db)
        A = a, B = b, X = [a,b,c,d,e], Z = [c,d,e]
        >>> prove_str('reverse([a,b,c,d], X)', db)
        X = [d,c,b,a]
        >>> prove_str('X is 2 + 2', db)
        X = 4
        >>> prove_str("(display('X could be any of... '), member(X, [1,2,3]), display(X), fail); nl, fail", db)
        X could be any of...  1 2 3
        >>> prove_str('length([a,b,c], X)', db)
        X = 3
        >>> prove_str('length(L, 2)', db)
        L = [_G1,_G2]
        >>> prove_str('findall(X, member(X, [a,b,c]), S)', db)
        S = [a,b,c]
        >>> prove_str('X = 5, fail; X = 7', db)
        X = 7
        >>> prove_str('var(X), Y = 5', db)
        Y = 5
        >>> prove_str('X = 3, var(X), Y = 5', db)
        >>> prove_str('integer(3), Y = 1; integer(X), Y = 2; integer(w), Y = 3', db)
        Y = 1
        >>> prove_str('\+(X = 5)', db)
        >>> prove_str('X = 3, \+(X = 5)', db)
        X = 3
        >>> prove_str('concat([a,b,c], [d,e], Z)', db)
        Z = [a,b,c,d,e]
        >>> prove_str('concat(X, [y,z], [w,x,y,z])', db)
        X = [w,x]
        >>> db.add_rules(['triplicate(X, W) :- W = [X,X,X]'])
        >>> prove_str('X = 1, findall(S, triplicate(X, S), B)', db)
        B = [[1,1,1]], X = 1
        >>> prove_str('findall(S, triplicate(X, S), B), X = 1, B = [[2,2,2]]', db)
        B = [[2,2,2]], X = 1
    """
    #print >>sys.stderr, "proving...", unparse(goal)
    functor = get_functor(goal)

    for r in database.get_rules(functor):
        for bound_vars in r(goal, database):
            yield bound_vars

def prove_str(goal_str, database):
    goal, scope = parse(goal_str)
    for bindings in prove(goal, database):
        print bound_vars_str(bindings, scope)

def prove_interactively(goal, scope, database):
    solution_num = 0
    for bound_vars in prove(goal, database):
        solution_num += 1
        print '%d.  %s' % (solution_num, bound_vars_str(bound_vars, scope))
        if solution_num >= 100:
            print '(too many solutions)'
            break
    print '(%d solutions)' % solution_num

def main():
    db = Database()
    db.add_rules(LIST_RULES)
    goal, scope = parse("X = [Y], Y = [X]")
    print 'Proving:', unparse(goal, scope)
    prove_interactively(goal, scope, db)

if __name__ == '__main__':
    main()
