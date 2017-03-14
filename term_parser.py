import string

from term import *

__all__ = ['parse', 'unparse']

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
    def __init__(self, operators, term_str, scope):
        self.operators = operators
        self.tokeniser = Tokeniser(term_str)
        self.scope = scope

    def reset(self, term_str):
        self.tokeniser = Tokeniser(term_str)

    def parse(self, terminators=''):
        value_stack = []
        operator_stack = []

        def reduce():
            stack_oper = operator_stack.pop()
            _, typ = self.operators[stack_oper]
            if typ in ('xfx', 'xfy', 'yfx'):
                v2 = value_stack.pop()
                v1 = value_stack.pop()
                item = Compound(stack_oper, v1, v2)
            elif typ in ('fx', 'xf', 'fy', 'yf'):
                v1 = value_stack.pop()
                item = Compound(stack_oper, v1)
            else:
                raise Exception('Unhandled operator type %s' % typ)
            value_stack.append(item)
            #print>>sys.stderr, 'reduced using operator', stack_oper

        while self.tokeniser.peek() is not None and self.tokeniser.peek() not in terminators:
            next_tok = self.tokeniser.peek()
            if next_tok not in self.operators:
                item = self.parse_simple()
                value_stack.append(item)
                #print>>sys.stderr, 'push value', item
                continue

            operator = self.tokeniser.next()
            prec, typ = self.operators[operator]
            while len(operator_stack) > 0:
                stack_oper = operator_stack[-1]
                stack_prec, stack_type = self.operators[stack_oper]
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
            return Compound(name, *subterms)
        else:
            if name[0] == "'":
                name = name[1:]
            if name[-1] == "'":
                name = name[:-1]
            return Atom(name)

def parse(operators, *term_strs):
    """
        Parse a Prolog term string into a Term object.

        >>> ops = {}
        >>> ops['='] = (700, 'xfx')
        >>> ops[','] = (1000, 'xfy')
        >>> ops[';'] = (1100, 'xfy')
        >>> ops[':-'] = (1200, 'xfx')
        >>> ops['is'] = (700, 'xfx')
        >>> ops['+'] = (500, 'yfx')
        >>> ops['-'] = (500, 'yfx')
        >>> ops['*'] = (400, 'yfx')
        >>> ops['=:='] = (700, 'xfx')
        >>> ops['=\\='] = (700, 'xfx')
        >>> ops['>'] = (700, 'xfx')
        >>> ops['>='] = (700, 'xfx')
        >>> ops['<'] = (700, 'xfx')
        >>> ops['=<'] = (700, 'xfx')
        >>> ops['\\+'] = (900, 'fy')

        >>> parse(ops, 'x')[0]
        Atom('x')
        >>> parse(ops, "'hello there'")[0]
        Atom('hello there')
        >>> parse(ops, 'X')[0]
        Variable()
        >>> parse(ops, '_X')[0]
        Variable()
        >>> parse(ops, '1')[0]
        Integer(1)
        >>> parse(ops, '(x)')[0]
        Atom('x')
        >>> parse(ops, 'f(a)')[0]
        Compound('f', Atom('a'))
        >>> parse(ops, '[]')[0]
        Atom('[]')
        >>> parse(ops, 'X = a; X = b')[0]
        Compound(';', Compound('=', Variable(), Atom('a')), Compound('=', Variable(), Atom('b')))
        >>> parse(ops, '[a]')[0]
        Compound('[|]', Atom('a'), Atom('[]'))
        >>> parse(ops, '[a|X]')[0]
        Compound('[|]', Atom('a'), Variable())
        >>> parse(ops, 'f(a, 5)')[0]
        Compound('f', Atom('a'), Integer(5))
        >>> parse(ops, 'X = 4')[0]
        Compound('=', Variable(), Integer(4))
        >>> parse(ops, '(X = 4), f(X)')[0]
        Compound(',', Compound('=', Variable(), Integer(4)), Compound('f', Variable()))
        >>> parse(ops, 'X = 4, g')[0]
        Compound(',', Compound('=', Variable(), Integer(4)), Atom('g'))
        >>> parse(ops, '[X,Y]')[0]
        Compound('[|]', Variable(), Compound('[|]', Variable(), Atom('[]')))
        >>> parse(ops, 'X is Y+2')[0]
        Compound('is', Variable(), Compound('+', Variable(), Integer(2)))
        >>> parse(ops, '\+X')[0]
        Compound('\\\+', Variable())
        >>> parse(ops, 'W , \+ X')[0]
        Compound(',', Variable(), Compound('\\\+', Variable()))
        >>> parse(ops, '\+ X, W')[0]
        Compound(',', Compound('\\\+', Variable()), Variable())
        >>> parse(ops, '\+ X + W')[0]
        Compound('\\\+', Compound('+', Variable(), Variable()))
        >>> parse(ops, 'a, b, c')[0]
        Compound(',', Atom('a'), Compound(',', Atom('b'), Atom('c')))
        >>> parse(ops, 'a, b, c')[0]
        Compound(',', Atom('a'), Compound(',', Atom('b'), Atom('c')))
        >>> parse(ops, '4 - 3 + 1')[0]
        Compound('+', Compound('-', Integer(4), Integer(3)), Integer(1))
        >>> parse(ops, '\+X = Y')[0]
        Compound('\\\+', Compound('=', Variable(), Variable()))
        >>> parse(ops, 'X = Y = Z')[0]
        Traceback (most recent call last):
          File "<stdin>", line 1, in ?
        SyntaxError: operator precedence clash
    """
    scope = Scope()
    rvs = []
    for ts in term_strs:
        p = Parser(operators, ts, scope)
        try:
            term = p.parse()
        except SyntaxError:
            print 'While parsing: %s' % ts
            raise
        rvs.append(term)
    rvs.append(scope)
    return tuple(rvs)

def unparse(operators, term, scope, printing=None):
    if printing is None:
        printing = set()
    term = term.resolve()
    if term.is_atom(LIST_NIL):
        return '[]'
    elif term.is_functor(LIST_CONS, 2):
        parts = []
        n = term
        while n.is_functor(LIST_CONS, 2):
            parts.append(n.subterms[0])
            n = n.subterms[1].resolve()
        tail = n
        if tail.is_atom(LIST_NIL):
            return '[%s]' % ','.join(unparse_recurse(operators, p, scope, printing, term) for p in parts)
        else:
            return '[%s|%s]' % (','.join(unparse_recurse(operators, p, scope, printing, term) for p in parts), unparse_recurse(operators, tail, scope, printing, term))
    elif term.is_operator(operators) and len(term.subterms) == 2:
        prec, typ = operators[term.name]
        lhs, rhs = term.subterms
        return '(%s %s %s)' % (unparse_recurse(operators, lhs, scope, printing, term), term.name, unparse_recurse(operators, rhs, scope, printing, term))
    elif term.is_operator(operators) and len(term.subterms) == 1:
        prec, typ = operators[term.name]
        rhs = term.subterms[0]
        return '(%s %s)' % (term.name, unparse_recurse(operators, rhs, scope, printing, term))
    elif isinstance(term, Compound):
        return '%s(%s)' % (term.name, ', '.join('%s' % unparse_recurse(operators, x, scope, printing, term) for x in term.subterms))
    elif isinstance(term, Variable):
        return scope.get_name(term)
    elif isinstance(term, Integer):
        return str(term.value)
    elif isinstance(term, Atom):
        return term.name
    else:
        return '???'

def unparse_recurse(operators, term, scope, printing, recursing_on):
    if recursing_on in printing or len(printing) > 10:
        return '...'
    printing.add(recursing_on)
    rv = unparse(operators, term, scope, printing)
    printing.remove(recursing_on)
    return rv
