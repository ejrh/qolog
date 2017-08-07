class Term(object):
    def get_vars(self):
        return []

    def copy_to_new_scope(self, scope):
        return self

    def resolve(self):
        return self

    def get_functor(self):
        return None

    def is_atom(self, name):
        return False

    def is_functor(self, name, arity):
        return False

    def is_operator(self, operators):
        return False

class Atom(Term):
    def __init__(self, name):
        self.name = name

    def get_functor(self):
        return self.name, 0

    def is_atom(self, name):
        return self.name == name

    def __repr__(self):
        return 'Atom(%s)' % repr(self.name)

    def __str__(self):
        return self.name

class Compound(Term):
    def __init__(self, name, *subterms):
        self.name = name
        self.subterms = subterms

    def get_vars(self):
        vs = []
        for s in self.subterms:
            vs.extend(s.get_vars())
        return vs

    def copy_to_new_scope(self, scope):
        return Compound(self.name, *[s.copy_to_new_scope(scope) for s in self.subterms])

    def get_functor(self):
        return self.name, len(self.subterms)

    def is_functor(self, name, arity):
        return self.name == name and len(self.subterms) == arity

    def is_operator(self, operators):
        return self.name in operators

    def __repr__(self):
        return 'Compound(%s, %s)' % (repr(self.name), ', '.join(repr(x) for x in self.subterms))

    def __str__(self):
        return '%s(%s)' % (self.name, ', '.join('%s' % x.resolve() for x in self.subterms))

class Variable(Term):
    def __init__(self):
        self.binding = None

    def get_vars(self):
        return [self]

    def copy_to_new_scope(self, scope):
        term = self.resolve()
        if isinstance(term, Variable):
            return scope.var(id(term))
        else:
            return term.copy_to_new_scope(scope)

    def resolve(self):
        if self.binding is None:
            return self
        else:
            return self.binding.resolve()

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

    def var_mappings(self, vs):
        result = {}
        for name,var in self.names_to_vars.items():
            term = var.resolve()
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
        Compound('[|]', Atom('hello'), Atom('[]'))
        >>> make_list([], Atom('[]'))
        Atom('[]')
        >>> make_list([], Compound('[|]', Atom('hello'), Atom('[]')))
        Compound('[|]', Atom('hello'), Atom('[]'))
    """
    if tail is None:
        lst = Atom(LIST_NIL)
    else:
        lst = tail
    for p in reversed(parts):
        lst = Compound(LIST_CONS, p, lst)
    return lst

def term_equality(t1, t2, typ, test):
    if not isinstance(t1, typ):
        return False
    if not isinstance(t2, typ):
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

def find_variables(term):
    vars_set = set()
    term = term.resolve()
    if isinstance(term, Variable):
        vars_set.add(term)
    elif isinstance(term, Compound):
        for st in term.subterms:
            vars_set.update(find_variables(st))
    return vars_set

def get_head(term):
    if term.is_functor(':-', 2):
        return term.subterms[0]
    else:
        return term

def get_body_subgoals(term):
    if term.is_functor(':-', 2):
        return find_subgoals(term.subterms[1])
    else:
        return []
