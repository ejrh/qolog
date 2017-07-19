import sys
import unittest

from term import *

class Enum(object):
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        return self.name

def enums(s):
    return [Enum(w) for w in s.split()]

REF, STR = enums('REF STR')
READ, WRITE = enums('READ WRITE')

put_structure, set_variable, set_value = enums('put_structure set_variable set_value')
get_structure, unify_variable, unify_value = enums('get_structure unify_variable unify_value')

class WAM(object):
    def __init__(self):
        self.heap = []
        self.reg_stack = []
        self.mode = None
        self.next_subterm = None

    def ensure_stack(self, idx):
        if len(self.reg_stack) <= idx:
            extra = idx - len(self.reg_stack) + 1
            self.reg_stack.extend((None, None) for i in range(extra))

    def deref(self, idx):
        a, b = self.heap[idx]
        while a is REF and b != idx:
            idx = b
            a, b = self.heap[idx]
        return idx

    def deref_reg(self, reg_idx):
        a, b = self.reg_stack[reg_idx]
        if a is REF:
            return self.deref(b)
        return None

    def bind(self, idx1, idx2):
        """
            Bind a variable at idx1 to idx2.
        """
        if self.heap[idx1] != (REF, idx1):
            idx1,idx2 = idx2,idx1
        assert self.heap[idx1] == (REF, idx1)
        self.heap[idx1] = (REF, idx2)

    def unify(self, idx1, idx2):
        """
            Unify two terms (both assumed to be on the heap).

            >>> w = WAM()
            >>> w.heap = [(REF, 0), (REF, 1)]
            >>> w.unify(0, 1)
            True
            >>> w.heap
            [(REF, 0), (REF, 0)]

            >>> w.heap = [(STR, 2), (REF, 1), ('a', 0)]
            >>> w.unify(0, 1)
            True
            >>> w.heap
            [(STR, 2), (REF, 0), ('a', 0)]

            >>> w.heap = [(REF, 0), (STR, 2), ('a', 0)]
            >>> w.unify(0, 1)
            True
            >>> w.heap
            [(REF, 1), (STR, 2), ('a', 0)]

            >>> w.heap = [(REF, 5), (STR, 2), ('f', 2), (REF, 3), ('a', 0), (STR, 6), ('f', 2), ('b', 0), (REF, 8)]
            >>> w.unify(0, 1)
            True
            >>> w.heap
            [(REF, 5), (STR, 2), ('f', 2), (REF, 7), ('a', 0), (STR, 6), ('f', 2), ('b', 0), (REF, 4)]
        """
        pdl = []
        pdl.append(idx1)
        pdl.append(idx2)
        fail = False
        while len(pdl) > 0 and not fail:
            d1 = self.deref(pdl.pop())
            d2 = self.deref(pdl.pop())
            if d1 == d2:
                continue
            a1, b1 = self.heap[d1]
            a2, b2 = self.heap[d2]
            if a1 is REF or a2 is REF:
                self.bind(d1, d2)
                continue
            assert a1 is STR and a2 is STR
            functor1 = self.heap[b1]
            functor2 = self.heap[b2]
            if functor1 == functor2:
                for i in range(functor1[1]):
                    pdl.append(b1 + 1 + i)
                    pdl.append(b2 + 1 + i)
            else:
                fail = True
                break
        return not fail

    def put_structure(self, functor, reg_idx):
        """
            Push a new STR (and adjoining functor) cell onto the heap and copy that cell into the
            allocated register address.

            >>> w = WAM()
            >>> w.put_structure(('f', 2), 0)
            >>> w.heap
            [(STR, 1), ('f', 2)]
            >>> w.reg_stack
            [(REF, 0)]
        """
        h = len(self.heap)
        self.heap.append((STR, h+1))
        self.heap.append(functor)
        self.ensure_stack(reg_idx)
        self.reg_stack[reg_idx] = (REF, h) #self.heap[h]

    def set_variable(self, reg_idx):
        """
            Push a new REF cell onto the heap containing its own address, and copy it into the
            given register.

            >>> w = WAM()
            >>> w.set_variable(0)
            >>> w.heap
            [(REF, 0)]
            >>> w.reg_stack
            [(REF, 0)]
        """
        h = len(self.heap)
        self.heap.append((REF, h))
        self.ensure_stack(reg_idx)
        self.reg_stack[reg_idx] = self.heap[h]

    def set_value(self, reg_idx):
        """
            Push a new cell onto the heap and copy into it the register's value.

            >>> w = WAM()
            >>> w.reg_stack = [(REF, 0)]
            >>> w.set_value(0)
            >>> w.heap
            [(REF, 0)]
        """
        self.ensure_stack(reg_idx)
        self.heap.append(self.reg_stack[reg_idx])

    def get_structure(self, functor, reg_idx):
        """
            Get a structure from the heap and set the read/write mode appropriately.

            >>> w = WAM()
            >>> w.heap = [(REF, 0)]
            >>> w.reg_stack = [None, (REF, 0)]
            >>> w.get_structure(('f', 2), 1)
            >>> w.mode
            WRITE
            >>> w.heap
            [(REF, 1), (STR, 2), ('f', 2)]

            >>> w.heap = [(STR, 1), ('f', 2)]
            >>> w.reg_stack = [None, (REF, 0)]
            >>> w.get_structure(('f', 2), 1)
            >>> w.mode
            READ
            >>> w.next_subterm
            2
        """
        self.next_subterm = 1
        self.ensure_stack(reg_idx)
        idx = self.deref_reg(reg_idx)
        if idx is not None:
            a, b = self.heap[idx]
        else:
            a, b = self.reg_stack[reg_idx]
        if a is REF:
            h = len(self.heap)
            self.heap.append((STR, h+1))
            self.heap.append(functor)
            self.bind(idx, h)
            self.mode = WRITE
        elif a is STR and self.heap[b] == functor:
            self.next_subterm = b + 1
            self.mode = READ
        else:
            if a is STR:
                raise Exception('Functor %s does not match %s' % (self.heap[b], functor))
            elif type(a) is str:
                raise Exception('Register %d points to functor cell!' % reg_idx)
            else:
                raise Exception('Register %d has invalid contents!' % reg_idx)

    def unify_variable(self, reg_idx):
        """
            Unify with a variable on the heap.

            >>> w = WAM()
            >>> w.heap = [('a', 0)]
            >>> w.reg_stack = [None, (REF, 0)]
            >>> w.mode = READ
            >>> w.next_subterm = 0
            >>> w.unify_variable(1)
            >>> w.reg_stack
            [None, (REF, 0)]
            >>> w.next_subterm
            1

            >>> w.heap = []
            >>> w.reg_stack = [None, ('a', 0)]
            >>> w.mode = WRITE
            >>> w.next_subterm = 0
            >>> w.unify_variable(1)
            >>> w.heap
            [(REF, 0)]
            >>> w.next_subterm
            1
        """
        self.ensure_stack(reg_idx)
        if self.mode == READ:
            self.reg_stack[reg_idx] = (REF, self.next_subterm) #self.heap[self.next_subterm]
        elif self.mode == WRITE:
            h = len(self.heap)
            self.heap.append((REF, h))
            self.reg_stack[reg_idx] = self.heap[h]
        else:
            raise Exception('Mode not set!')
        self.next_subterm += 1

    def unify_value(self, reg_idx):
        """
            Unify with a value on the heap.

            >>> w = WAM()
            >>> w.heap = [('a', 0)]
            >>> w.reg_stack = [None, (REF, 0)]
            >>> w.mode = READ
            >>> w.next_subterm = 0
            >>> w.unify_variable(1)
            >>> w.reg_stack
            [None, (REF, 0)]
            >>> w.next_subterm
            1

            >>> w.heap = []
            >>> w.reg_stack = [None, ('a', 0)]
            >>> w.mode = WRITE
            >>> w.next_subterm = 0
            >>> w.unify_variable(1)
            >>> w.heap
            [(REF, 0)]
            >>> w.next_subterm
            1
        """
        self.ensure_stack(reg_idx)
        if self.mode == READ:
            idx = self.deref_reg(reg_idx)
            assert idx is not None
            self.unify(idx, self.next_subterm)
        elif self.mode == WRITE:
            h = len(self.heap)
            self.heap.append(self.reg_stack[reg_idx])
        else:
            raise Exception('Mode not set!')
        self.next_subterm += 1

    def get_term_repr(self, idx):
        idx = self.deref(idx)
        a, b = self.heap[idx]
        if a is REF:
            return '_G%d' % b
        elif a is STR:
            name,arity = self.heap[b]
            if arity == 0:
                return name
            else:
                return '%s(%s)' % (name, ', '.join(self.get_term_repr(b+1+x) for x in range(arity)))
        else:
            raise Exception('Cell at %d is not REF or STR' % idx)

    def execute(self, instrs):
        for instr in instrs:
            op = instr[0]
            args = instr[1:]
            f = getattr(self, op.name)
            f(*args)

class Compiler(object):
    def allocate_registers(self, term, reg_allocation):
        def get_reg(term):
            if term not in reg_allocation:
                reg_allocation[term] = len(reg_allocation) + 1
            return reg_allocation[term]

        term = term.resolve()
        get_reg(term)

        if isinstance(term, Compound):
            # Immediate children are allocated registers
            for subterm in term.subterms:
                get_reg(subterm.resolve())

            # Then other descendents
            for subterm in term.subterms:
                subterm = subterm.resolve()
                self.allocate_registers(subterm, reg_allocation)

    def compile_query(self, query, reg_allocation=None, vars_set=None):
        """
            >>> c = Compiler()
            >>> c.compile_query(Atom('a'))
            [(put_structure, ('a', 0), 1)]
            >>> c.compile_query(Variable())
            [(set_variable, 1)]
            >>> c.compile_query(Compound('f', Atom('a'), Variable()))
            [(put_structure, ('a', 0), 2), (put_structure, ('f', 2), 1), (set_value, 2), (set_variable, 3)]
            >>> Z = Variable()
            >>> W = Variable()
            >>> c.compile_query(Compound('p', Z, Compound('h', Z, W), Compound('f', W)))
            [(put_structure, ('h', 2), 3), (set_variable, 2), (set_variable, 5), (put_structure, ('f', 1), 4), (set_value, 5), (put_structure, ('p', 3), 1), (set_value, 2), (set_value, 3), (set_value, 4)]
        """

        if reg_allocation is None:
            reg_allocation = {}

        if vars_set is None:
            vars_set = set()
            self.allocate_registers(query, reg_allocation)

        query = query.resolve()
        if isinstance(query, Atom):
            return [(put_structure, query.get_functor(), reg_allocation[query])]
        elif isinstance(query, Compound):
            instrs = []
            # Build nested terms
            for subterm in query.subterms:
                subterm = subterm.resolve()
                if isinstance(subterm, Variable):
                    continue
                instrs.extend(self.compile_query(subterm, reg_allocation, vars_set))
                vars_set.add(subterm)
            # Build this term
            instrs.append((put_structure, query.get_functor(), reg_allocation[query]))
            for subterm in query.subterms:
                subterm = subterm.resolve()
                if subterm in vars_set:
                    instrs.append((set_value, reg_allocation[subterm]))
                else:
                    vars_set.add(subterm)
                    instrs.append((set_variable, reg_allocation[subterm]))
            return instrs
        elif isinstance(query, Variable):
            if query in vars_set:
                return [(set_value, reg_allocation[query])]
            else:
                vars_set.add(query)
                return [(set_variable, reg_allocation[query])]

    def compile_program(self, program, reg_allocation=None, vars_set=None):
        """
            >>> c = Compiler()
            >>> c.compile_program(Atom('a'))
            [(get_structure, ('a', 0), 1)]
            >>> c.compile_program(Variable())
            [(unify_variable, 1)]
            >>> c.compile_program(Compound('f', Atom('a'), Variable()))
            [(get_structure, ('f', 2), 1), (unify_variable, 2), (unify_variable, 3), (get_structure, ('a', 0), 2)]
            >>> X = Variable()
            >>> Y = Variable()
            >>> c.compile_program(Compound('p', Compound('f', X), Compound('h', Y, Compound('f', Atom('a'))), Y))
            [(get_structure, ('p', 3), 1), (unify_variable, 2), (unify_variable, 3), (unify_variable, 4), (get_structure, ('f', 1), 2), (unify_variable, 5), (get_structure, ('h', 2), 3), (unify_value, 4), (unify_variable, 6), (get_structure, ('f', 1), 6), (unify_variable, 7), (get_structure, ('a', 0), 7)]
        """

        if reg_allocation is None:
            reg_allocation = {}

        if vars_set is None:
            vars_set = set()
            self.allocate_registers(program, reg_allocation)

        program = program.resolve()
        if isinstance(program, Atom):
            return [(get_structure, program.get_functor(), reg_allocation[program])]
        elif isinstance(program, Compound):
            instrs = []
            # Build this term
            instrs.append((get_structure, program.get_functor(), reg_allocation[program]))
            for subterm in program.subterms:
                subterm = subterm.resolve()
                if subterm in vars_set:
                    instrs.append((unify_value, reg_allocation[subterm]))
                else:
                    vars_set.add(subterm)
                    instrs.append((unify_variable, reg_allocation[subterm]))
            # Build nested terms
            for subterm in program.subterms:
                subterm = subterm.resolve()
                if isinstance(subterm, Variable):
                    continue
                instrs.extend(self.compile_program(subterm, reg_allocation, vars_set))
                vars_set.add(subterm)
            return instrs
        elif isinstance(program, Variable):
            if program in vars_set:
                return [(unify_value, reg_allocation[program])]
            else:
                vars_set.add(program)
                return [(unify_variable, reg_allocation[program])]

    def write_to_heap(self, term, wam, var_idxes=None):
        """
            Write a term to a WAM heap, and return the index of its root cell.  Also populate
            var_idxes with the indexes of all distinct variables in the term.

            >>> w = WAM()
            >>> c = Compiler()
            >>> c.write_to_heap(Atom('a'), w)
            0
            >>> w.heap
            [(STR, 1), ('a', 0)]

            >>> vi = {}
            >>> c.write_to_heap(Variable(), w, vi)
            2
            >>> w.heap
            [(STR, 1), ('a', 0), (REF, 2)]
            >>> vi
            {Variable(): 2}

            >>> vi = {}
            >>> c.write_to_heap(Compound('f', Atom('a'), Variable()), w, vi)
            6
            >>> w.heap
            [(STR, 1), ('a', 0), (REF, 2), (STR, 4), ('a', 0), (REF, 5), (STR, 7), ('f', 2), (REF, 3), (REF, 5)]
            >>> vi
            {Variable(): 5}
        """

        if var_idxes is None:
            var_idxes = {}

        term = term.resolve()
        if isinstance(term, Atom):
            h = len(wam.heap)
            wam.heap.append((STR, h+1))
            wam.heap.append(term.get_functor())
        elif isinstance(term, Variable):
            if term in var_idxes:
                h = var_idxes[term]
                wam.heap.append((REF, h))
            else:
                h = len(wam.heap)
                wam.heap.append((REF, h))
                var_idxes[term] = h
        elif isinstance(term, Compound):
            sub_idxes = [self.write_to_heap(st, wam, var_idxes) for st in term.subterms]
            h = len(wam.heap)
            wam.heap.append((STR, h+1))
            wam.heap.append(term.get_functor())
            for si in sub_idxes:
                wam.heap.append((REF, si))
        else:
            raise Exception('Unhandled term type: %s' % type(term))
        return h

def print_instrs(instrs):
    def arg_str(arg):
        if type(arg) is tuple and type(arg[0]) is str and type(arg[1]) is int:
            return '%s/%d' % arg
        return str(arg)

    for instr in instrs:
        op = instr[0]
        args = instr[1:]
        if len(args) == 0:
            print op
        else:
            print '%s %s' % (op, ', '.join(arg_str(x) for x in args))

def print_heap(heap):
    for i, cell in enumerate(heap):
        if i % 10 == 0:
            if i != 0:
                print
            print '[%2d]   ' % i,
        if cell[0] is None:
            s = '     '
        elif type(cell[0]) is str:
            s = '%s/%s' % cell
        else:
            s = '%s %s' % cell
        print '%-8s' % s,
    print

class WAMTest(unittest.TestCase):
    def execute_fig_2_3(self, wam):
        """
            Compiled code for L_0 query ?- p(Z, h(Z, W), f(W)).
        """
        wam.put_structure(('h', 2), 3)   # ?- X3 = h
        wam.set_variable(2)              #          (Z,
        wam.set_variable(5)              #             W),
        wam.put_structure(('f', 1), 4)   #    X4 = f
        wam.set_value(5)                 #          (W),
        wam.put_structure(('p', 3), 1)   #    X1 = p
        wam.set_value(2)                 #          (Z,
        wam.set_value(3)                 #             X3,
        wam.set_value(4)                 #                X4).

    def execute_fig_2_4(self, wam):
        """
            Compiled code for L_0 program p(f(X), h(Y, f(a)), Y).
        """
        wam.get_structure(('p', 3), 1)   # X1 = p
        wam.unify_variable(2)            #       (X2,
        wam.unify_variable(3)            #           X3,
        wam.unify_variable(4)            #              Y),
        wam.get_structure(('f', 1), 2)   # X2 = f
        wam.unify_variable(5)            #       (X),
        wam.get_structure(('h', 2), 3)   # X3 = h
        wam.unify_value(4)               #       (Y,
        wam.unify_variable(6)            #          X6),
        wam.get_structure(('f', 1), 6)   # X6 = f
        wam.unify_variable(7)            #       (X7),
        wam.get_structure(('a', 0), 7)   # X7 = a.

    def test_ex_2_1(self):
        """
            Exercise 2.1

            Verify that the effect of executing the sequence of instructions shown in Figure 2.3
            (starting with H = 0) does indeed yield a correct heap representation for the term
            p(Z, h(Z,W), f(W)) -- the one shown earlier as Figure 2.1, in fact.
        """

        wam = WAM()
        self.execute_fig_2_3(wam)
        #s = wam.get_term_repr(wam.deref_reg(0))
        s = wam.get_term_repr(7)
        self.assertEqual(s, 'p(_G2, h(_G2, _G3), f(_G3))')

    def test_ex_2_2(self):
        """
            Exercise 2.2

            Give heap representations for the terms f(X,g(X, a)) and f(b, Y).  Let a1 and a2 be
            their respective heap addresses, and let aX and aY be the heap addresses corresponding
            to variables X and Y, respectively.  Trace the effects of executing unify(a1, a2),
            verifying that it terminates with the eventual dereferenced bindings from aX and aY
            corresponding to X = b and Y = g(b, a).
        """
        wam = WAM()
        compiler = Compiler()
        X = Variable()
        Y = Variable()
        var_idxes = {}
        a1 = compiler.write_to_heap(Compound('f', X, Compound('g', X, Atom('a'))), wam, var_idxes)
        a2 = compiler.write_to_heap(Compound('f', Atom('b'), Y), wam, var_idxes)
        aX = var_idxes[X]
        aY = var_idxes[Y]
        wam.unify(a1, a2)
        self.assertEqual(wam.get_term_repr(aX), 'b')
        self.assertEqual(wam.get_term_repr(aY), 'g(b, a)')

    def test_ex_2_3(self):
        """
            Exercise 2.3

            Verify that the effect of executing the sequence of instructions shown in Figure 2.4
            right after that in Figure 2.3 produces the MGU of the terms p(Z, h(Z, W), f(W)) and
            p(f(X), h(Y, f(a)), Y).  That is, the (dereferenced) bindings corresponding to
            W = f(a), X = f(a), Y = f(f(a)), Z = f(f(a)).
        """

        wam = WAM()
        self.execute_fig_2_3(wam)
        aW = wam.deref_reg(5)
        aZ = wam.deref_reg(2)
        self.execute_fig_2_4(wam)
        aX = wam.deref_reg(5)
        aY = wam.deref_reg(4)
        self.assertEqual(wam.get_term_repr(aW), 'f(a)')
        self.assertEqual(wam.get_term_repr(aX), 'f(a)')
        self.assertEqual(wam.get_term_repr(aY), 'f(f(a))')
        self.assertEqual(wam.get_term_repr(aZ), 'f(f(a))')

    def test_ex_2_4(self):
        """
            Exercise 2.4

            What are the respective sequences of M_0 instructions for L_0 query term
            ?- p(f(X), h(Y, f(a)), Y) and program term p(Z, h(Z, W), f(W) ?
        """

        compiler = Compiler()

        X = Variable()
        Y = Variable()
        query = Compound('p', Compound('f', X), Compound('h', Y, Compound('f', Atom('a'))), Y)
        instrs = compiler.compile_query(query)
        self.assertEqual(instrs, [
            (put_structure, ('f', 1), 2),
            (set_variable, 5),
            (put_structure, ('a', 0), 7),
            (put_structure, ('f', 1), 6),
            (set_value, 7),
            (put_structure, ('h', 2), 3),
            (set_variable, 4),
            (set_value, 6),
            (put_structure, ('p', 3), 1),
            (set_value, 2),
            (set_value, 3),
            (set_value, 4)
        ])

        W = Variable()
        Z = Variable()
        program = Compound('p', Z, Compound('h', Z, W), Compound('f', W))
        instrs = compiler.compile_program(program)
        self.assertEqual(instrs, [
            (get_structure, ('p', 3), 1),
            (unify_variable, 2),
            (unify_variable, 3),
            (unify_variable, 4),
            (get_structure, ('h', 2), 3),
            (unify_value, 2),
            (unify_variable, 5),
            (get_structure, ('f', 1), 4),
            (unify_value, 5)
        ])

    def test_ex_2_5(self):
        """
            Exercise 2.5

            After doing Exercise 2.4, verify that the effect of executing the sequence you
            produced yields the same solution as that of Exercise 2.3.
        """

        compiler = Compiler()

        X = Variable()
        Y = Variable()
        query = Compound('p', Compound('f', X), Compound('h', Y, Compound('f', Atom('a'))), Y)
        query_reg_allocation = {}
        query_instrs = compiler.compile_query(query, query_reg_allocation)

        W = Variable()
        Z = Variable()
        program = Compound('p', Z, Compound('h', Z, W), Compound('f', W))
        program_reg_allocation = {}
        program_instrs = compiler.compile_program(program, program_reg_allocation)

        wam = WAM()
        wam.execute(query_instrs)
        wam.execute(program_instrs)
        aW = wam.deref_reg(program_reg_allocation[W])
        aX = wam.deref_reg(query_reg_allocation[X])
        aY = wam.deref_reg(query_reg_allocation[Y])
        aZ = wam.deref_reg(program_reg_allocation[Z])
        self.assertEqual(wam.get_term_repr(aW), 'f(a)')
        self.assertEqual(wam.get_term_repr(aX), 'f(a)')
        self.assertEqual(wam.get_term_repr(aY), 'f(f(a))')
        self.assertEqual(wam.get_term_repr(aZ), 'f(f(a))')

def main():
    from term_parser import parse, unparse

    try:
        query_str = sys.argv[1]
        program_str = sys.argv[2]
        query, query_scope = parse({}, query_str)
        program, program_scope = parse({}, program_str)
    except:
        print 'Please enter a query and a program (with quotes around each if necessary)'
        print 'E.g.   wam.py   "p(Z, h(Z, W), f(W))"   "p(f(X), h(Y, f(a)), Y)"'
        sys.exit(1)

    print 'Running query:    %s' % unparse({}, query, query_scope)
    print 'Against program:  %s' % unparse({}, program, program_scope)

    compiler = Compiler()
    wam = WAM()

    print
    print 'Compiled query to:'
    query_reg_map = {}
    query_instrs = compiler.compile_query(query, query_reg_map)
    print_instrs(query_instrs)
    print 'Register allocations are: ', ', '.join('%s: %s' % (n, query_reg_map[v]) for n,v in query_scope.names_to_vars.items())

    print
    print 'Compiled program to:'
    program_reg_map = {}
    program_instrs = compiler.compile_program(program, program_reg_map)
    print_instrs(program_instrs)
    print 'Register allocations are: ', ', '.join('%s: %s' % (n, program_reg_map[v]) for n,v in program_scope.names_to_vars.items())

    print
    print 'Running query and program...'
    wam.execute(query_instrs)
    wam.execute(program_instrs)
    for n, v in query_scope.names_to_vars.items():
        print '%s = %s' % (n, wam.get_term_repr(wam.deref_reg(query_reg_map[v])))
    for n, v in program_scope.names_to_vars.items():
        print '%s = %s' % (n, wam.get_term_repr(wam.deref_reg(program_reg_map[v])))

    print
    print 'Final WAM state:'
    print 'Heap:'
    print_heap(wam.heap)
    print 'Registers:'
    print_heap(wam.reg_stack)

if __name__ == '__main__':
    main()
