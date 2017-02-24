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
OPERATOR_CHARS = ',=:-<>\\+'
SIMPLE_CHARS = WORD_CHARS + '(['

class Tokeniser(object):
    def __init__(self, term_str):
        self.term_str = term_str
        self.pos = 0
        self.cached = None

    def peek(self):
        if self.cached is None:
            self.cached = self.do_next()
        return self.cached

    def next(self):
        token = self.do_next()
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

class Parser(object):
    def __init__(self, database, term_str, scope):
        self.database = database
        self.tokeniser = Tokeniser(term_str)
        self.scope = scope

    def reset(self, term_str):
        self.tokeniser = Tokeniser(term_str)

    def parse(self, terminators=''):
        value_stack = []
        operator_stack = []

        def reduce():
            stack_oper = operator_stack.pop()
            _, type = self.database.operators[stack_oper]
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
            if next_tok not in self.database.operators:
                item = self.parse_simple()
                value_stack.append(item)
                #print>>sys.stderr, 'push value', item
                continue

            operator = self.tokeniser.next()
            prec, type = self.database.operators[operator]
            while len(operator_stack) > 0:
                stack_oper = operator_stack[-1]
                stack_prec, stack_type = self.database.operators[stack_oper]
                #print >>sys.stderr, "Stack: %s %s %s   Next: %s %s %s" % (stack_oper, stack_prec, stack_type, operator, prec, type)
                if stack_type == 'xfx' and stack_prec == prec:
                    raise SyntaxError('operator precedence clash')

                if stack_type == 'yfx' and stack_prec <= prec:
                    reduce()
                elif stack_prec < prec:
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

def parse(database, *term_strs):
    """
        Parse a Prolog term string into a Term object.

        >>> db = Database()
        >>> parse(db, 'x')[0]
        Atom('x')
        >>> parse(db, "'hello there'")[0]
        Atom('hello there')
        >>> parse(db, 'X')[0]
        Variable()
        >>> parse(db, '_X')[0]
        Variable()
        >>> parse(db, '1')[0]
        Integer(1)
        >>> parse(db, '(x)')[0]
        Atom('x')
        >>> parse(db, 'f(a)')[0]
        Compound('f', [Atom('a')])
        >>> parse(db, '[]')[0]
        Atom('[]')
        >>> parse(db, 'X = a; X = b')[0]
        Compound(';', [Compound('=', [Variable(), Atom('a')]), Compound('=', [Variable(), Atom('b')])])
        >>> parse(db, '[a]')[0]
        Compound('[|]', [Atom('a'), Atom('[]')])
        >>> parse(db, '[a|X]')[0]
        Compound('[|]', [Atom('a'), Variable()])
        >>> parse(db, 'f(a, 5)')[0]
        Compound('f', [Atom('a'), Integer(5)])
        >>> parse(db, 'X = 4')[0]
        Compound('=', [Variable(), Integer(4)])
        >>> parse(db, '(X = 4), f(X)')[0]
        Compound(',', [Compound('=', [Variable(), Integer(4)]), Compound('f', [Variable()])])
        >>> parse(db, 'X = 4, g')[0]
        Compound(',', [Compound('=', [Variable(), Integer(4)]), Atom('g')])
        >>> parse(db, '[X,Y]')[0]
        Compound('[|]', [Variable(), Compound('[|]', [Variable(), Atom('[]')])])
        >>> parse(db, 'X is Y+2')[0]
        Compound('is', [Variable(), Compound('+', [Variable(), Integer(2)])])
        >>> parse(db, '\+X')[0]
        Compound('\\\+', [Variable()])
        >>> parse(db, 'W , \+ X')[0]
        Compound(',', [Variable(), Compound('\\\+', [Variable()])])
        >>> parse(db, '\+ X, W')[0]
        Compound(',', [Compound('\\\+', [Variable()]), Variable()])
        >>> parse(db, '\+ X + W')[0]
        Compound('\\\+', [Compound('+', [Variable(), Variable()])])
        >>> parse(db, 'a, b, c')[0]
        Compound(',', [Atom('a'), Compound(',', [Atom('b'), Atom('c')])])
        >>> parse(db, 'a, b, c')[0]
        Compound(',', [Atom('a'), Compound(',', [Atom('b'), Atom('c')])])
        >>> parse(db, '4 - 3 + 1')[0]
        Compound('+', [Compound('-', [Integer(4), Integer(3)]), Integer(1)])
        >>> parse(db, '\+X = Y')[0]
        Compound('\\\+', [Compound('=', [Variable(), Variable()])])
        >>> parse(db, 'X = Y = Z')[0]
        Traceback (most recent call last):
          File "<stdin>", line 1, in ?
        SyntaxError: operator precedence clash
    """
    scope = Scope()
    rvs = []
    for ts in term_strs:
        p = Parser(database, ts, scope)
        try:
            term = p.parse()
        except SyntaxError:
            print 'While parsing: %s' % ts
            raise
        rvs.append(term)
    rvs.append(scope)
    return tuple(rvs)

def unparse(database, term, scope, printing=None):
    if printing is None:
        printing = set()
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
            return '[%s]' % ','.join(unparse_recurse(database, p, scope, printing, term) for p in parts)
        else:
            return '[%s|%s]' % (','.join(unparse_recurse(database, p, scope, printing, term) for p in parts), unparse_recurse(database, tail, scope, printing, term))
    elif term_is_operator(term, database) and len(term.subterms) == 2:
        prec, type = database.operators[term.name]
        lhs, rhs = term.subterms
        return '(%s %s %s)' % (unparse_recurse(database, lhs, scope, printing, term), term.name, unparse_recurse(database, rhs, scope, printing, term))
    elif term_is_operator(term, database) and len(term.subterms) == 1:
        prec, type = database.operators[term.name]
        rhs = term.subterms[0]
        return '(%s %s)' % (term.name, unparse_recurse(database, rhs, scope, printing, term))
    elif isinstance(term, Compound):
        return '%s(%s)' % (term.name, ', '.join('%s' % unparse_recurse(database, x, scope, printing, term) for x in term.subterms))
    elif isinstance(term, Variable):
        return scope.get_name(term)
    elif isinstance(term, Integer):
        return str(term.value)
    elif isinstance(term, Atom):
        return term.name
    else:
        return '???'

def unparse_recurse(database, term, scope, printing, recursing_on):
    if recursing_on in printing or len(printing) > 10:
        return '...'
    printing.add(recursing_on)
    rv = unparse(database, term, scope, printing)
    printing.remove(recursing_on)
    return rv

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

def term_is_operator(term, database):
    if not isinstance(term, Compound):
        return False
    return term.name in database.operators

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

def unify_strs(database, str1, str2):
    t1, t2, scope = parse(database, str1, str2)
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

def assert_rule(term, database):
    if not term_is_functor(term, 'assert', 1):
        return []
    rule = term.subterms[0]
    database.add_rule_at_end(rule)
    return [set()]

def retractall_rule(term, database):
    if not term_is_functor(term, 'retractall', 1):
        return []
    head = term.subterms[0]
    database.remove_matching_rules(head)
    return [set()]

def evaluate_term(term):
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
        elif op == '*':
            return lhs_value * rhs_value
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
    if not term_is_functor(term, 'display', 1):
        return []
    arg = resolve_variable(term.subterms[0])
    print unparse(database, arg, Scope()),
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
    bag = make_list(results)
    bound_vars = unify(bag_var, bag)
    if bound_vars is None:
        return
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

def between_rule(term, database):
    #if not term_is_functor(term, 'between', 3):
    #    return
    low, high, value = term.subterms
    low = resolve_variable(low)
    high = resolve_variable(high)
    if not isinstance(low, Integer) or not isinstance(high, Integer):
        return
    value = resolve_variable(value)
    if isinstance(value, Integer):
        if low.value <= value.value <= high.value:
            yield set()
        return
    for i in range(low.value, high.value+1):
        bound_vars = unify(value, Integer(i))
        yield bound_vars
        unbind_all(bound_vars)

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
        self.register_at_end((',', 2), '_ , _', comma_rule)
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
        self.register_at_end(('var', 1), 'var(_)', var_rule)
        self.register_at_end(('integer', 1), 'integer(_)', integer_rule)
        self.register_at_end(('between', 3), 'between(_, _, _)', between_rule)

    def register_operator(self, name, precedence, type):
        self.operators[name] = precedence, type

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
            rule, _ = parse(self, rule)
        else:
            rule = rule.copy_to_new_scope(Scope())
        if not term_is_functor(rule, ':-', 2):
            rule = Compound(':-', [rule, Atom('true')])
        head = rule.subterms[0]
        functor = get_functor(head)
        if functor is None:
            raise Exception('Cannot make a rule with head %s' % (head,))
        compiled_rule = compile_rule(rule)
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
        functor = get_functor(head)
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

LIST_RULES = [
    'length([], 0) :- true',
    'length([_|T], X) :- var(X), length(T, X0), X is X0 + 1',
    'length([_|T], X) :- integer(X), X >= 0, Xm1 is X - 1, length(T, Xm1)',
    'member(M, L) :- L = [M|L2]',
    'member(M, L) :- L = [_|L2], member(M, L2)',
    'reverse(X, Y) :- reverse(X, [], Y, Y)',
    'reverse([], A, A, []) :- true',
    'reverse([A|B], C, D, [_|E]) :- reverse(B, [A|C], D, E)',
    'concat([], B, B) :- true',
    'concat([H|A], B, [H|C]) :- concat(A, B, C)',
]

ARITHMETIC_RULES = [
#    'between(L, H, V) :- integer(V), L =< V, V =< H',
#    'between(L, H, V) :- var(V), L =< H, V = L',
#    'between(L, H, V) :- var(V), L < H, Lp1 is L + 1, between(Lp1, H, V)',
]

def bound_vars_str(database, vars, scope):
    return ', '.join('%s = %s' % (str(v), unparse(database, t, scope)) for v,t in sorted(scope.var_mappings(vars).items()))

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
        >>> prove_str('assert(human(socrates)), assert(human(pythagoras)), human(X)', db)
        X = socrates
        X = pythagoras
        >>> prove_str('''assert(divides(P, P) :- P > 0), \
                assert((divides(P, Q) :- P > 0, Q > P, QmP is Q - P, divides(P, QmP))), \
                assert(prime(P) :- known_prime(P)), \
                assert((prime(P) :- \+known_prime(P), findall(_, (between(2, P, D), known_prime(D), divides(D, P)), []), assert(known_prime(P) :- true), true)), \
                assert(known_prime(2) :- true), \
                findall(P, (between(2, 25, P), prime(P)), S)''', db)
        S = [2,3,5,7,11,13,17,19,23]
    """
    functor = get_functor(goal)

    for _, r in database.get_rules(functor):
        for bound_vars in r(goal, database):
            yield bound_vars

def prove_str(goal_str, database):
    goal, scope = parse(database, goal_str)
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
    goal, scope = parse(db, query_str)
    print 'Proving:', unparse(db, goal, scope)
    prove_interactively(goal, scope, db)

if __name__ == '__main__':
    main()
