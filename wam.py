import sys

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

class Instruction(object):
    def __init__(self, *args):
        self.args = args

    def __eq__(self, other):
        if self.__class__ is not other.__class__:
            return False
        if self.args != other.args:
            return False
        return True

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash((self.get_name(), self.get_args()))

    def __repr__(self):
        name = self.get_name()
        args_str = ', '.join(repr(x) for x in self.get_args())
        return '%s(%s)' % (name, args_str)

    def get_name(self):
        return self.__class__.__name__

    def get_args(self):
        return self.args

class put_structure(Instruction):
    """
        Push a new STR (and adjoining functor) cell onto the heap and copy that cell into the
        allocated register address.

        >>> w = WAM()
        >>> put_structure(('f', 2), 0).execute(w)
        >>> w.heap
        [(STR, 1), ('f', 2)]
        >>> w.reg_stack
        [(REF, 0)]
    """

    def execute(self, wam):
        functor, reg_idx = self.args
        h = len(wam.heap)
        wam.heap.append((STR, h + 1))
        wam.heap.append(functor)
        wam.ensure_stack(reg_idx)
        wam.reg_stack[reg_idx] = (REF, h)  # wam.heap[h]

class set_variable(Instruction):
    """
        Push a new REF cell onto the heap containing its own address, and copy it into the
        given register.

        >>> w = WAM()
        >>> set_variable(0).execute(w)
        >>> w.heap
        [(REF, 0)]
        >>> w.reg_stack
        [(REF, 0)]
    """

    def execute(self, wam):
        reg_idx, = self.args
        h = len(wam.heap)
        wam.heap.append((REF, h))
        wam.ensure_stack(reg_idx)
        wam.reg_stack[reg_idx] = wam.heap[h]

class set_value(Instruction):
    """
        Push a new cell onto the heap and copy into it the register's value.

        >>> w = WAM()
        >>> w.reg_stack = [(REF, 0)]
        >>> set_value(0).execute(w)
        >>> w.heap
        [(REF, 0)]
    """

    def execute(self, wam):
        reg_idx, = self.args
        wam.ensure_stack(reg_idx)
        wam.heap.append(wam.reg_stack[reg_idx])

class get_structure(Instruction):
    """
        Get a structure from the heap and set the read/write mode appropriately.

        >>> w = WAM()
        >>> w.heap = [(REF, 0)]
        >>> w.reg_stack = [None, (REF, 0)]
        >>> get_structure(('f', 2), 1).execute(w)
        >>> w.mode
        WRITE
        >>> w.heap
        [(REF, 1), (STR, 2), ('f', 2)]

        >>> w.heap = [(STR, 1), ('f', 2)]
        >>> w.reg_stack = [None, (REF, 0)]
        >>> get_structure(('f', 2), 1).execute(w)
        >>> w.mode
        READ
        >>> w.next_subterm
        2
    """

    def execute(self, wam):
        functor, reg_idx = self.args
        wam.next_subterm = 1
        wam.ensure_stack(reg_idx)
        idx = wam.deref_reg(reg_idx)
        if idx is not None:
            a, b = wam.heap[idx]
        else:
            a, b = wam.reg_stack[reg_idx]
        if a is REF:
            h = len(wam.heap)
            wam.heap.append((STR, h+1))
            wam.heap.append(functor)
            wam.bind(idx, h)
            wam.mode = WRITE
        elif a is STR and wam.heap[b] == functor:
            wam.next_subterm = b + 1
            wam.mode = READ
        else:
            if a is STR:
                raise Exception('Functor %s does not match %s' % (wam.heap[b], functor))
            elif type(a) is str:
                raise Exception('Register %d points to functor cell!' % reg_idx)
            else:
                raise Exception('Register %d has invalid contents!' % reg_idx)

class unify_variable(Instruction):
    """
        Unify with a variable on the heap.

        >>> w = WAM()
        >>> w.heap = [('a', 0)]
        >>> w.reg_stack = [None, (REF, 0)]
        >>> w.mode = READ
        >>> w.next_subterm = 0
        >>> unify_variable(1).execute(w)
        >>> w.reg_stack
        [None, (REF, 0)]
        >>> w.next_subterm
        1

        >>> w.heap = []
        >>> w.reg_stack = [None, ('a', 0)]
        >>> w.mode = WRITE
        >>> w.next_subterm = 0
        >>> unify_variable(1).execute(w)
        >>> w.heap
        [(REF, 0)]
        >>> w.next_subterm
        1
    """

    def execute(self, wam):
        reg_idx, = self.args
        wam.ensure_stack(reg_idx)
        if wam.mode == READ:
            wam.reg_stack[reg_idx] = (REF, wam.next_subterm) #self.heap[self.next_subterm]
        elif wam.mode == WRITE:
            h = len(wam.heap)
            wam.heap.append((REF, h))
            wam.reg_stack[reg_idx] = wam.heap[h]
        else:
            raise Exception('Mode not set!')
        wam.next_subterm += 1

class unify_value(Instruction):
    """
        Unify with a value on the heap.

        >>> w = WAM()
        >>> w.heap = [('a', 0)]
        >>> w.reg_stack = [None, (REF, 0)]
        >>> w.mode = READ
        >>> w.next_subterm = 0
        >>> unify_variable(1).execute(w)
        >>> w.reg_stack
        [None, (REF, 0)]
        >>> w.next_subterm
        1

        >>> w.heap = []
        >>> w.reg_stack = [None, ('a', 0)]
        >>> w.mode = WRITE
        >>> w.next_subterm = 0
        >>> unify_variable(1).execute(w)
        >>> w.heap
        [(REF, 0)]
        >>> w.next_subterm
        1
    """

    def execute(self, wam):
        reg_idx, = self.args
        wam.ensure_stack(reg_idx)
        if wam.mode == READ:
            idx = wam.deref_reg(reg_idx)
            assert idx is not None
            wam.unify(idx, wam.next_subterm)
        elif wam.mode == WRITE:
            h = len(wam.heap)
            wam.heap.append(wam.reg_stack[reg_idx])
        else:
            raise Exception('Mode not set!')
        wam.next_subterm += 1

class call(Instruction):
    def execute(self, wam):
        functor, = self.args
        wam.p = wam.labels[functor] - 1  # -1 because p will be incremented after this instruction
        #wam.reg_stack = wam.reg_stack[:functor[1]+1]

class proceed(Instruction):
    def execute(self, wam):
        pass

class put_variable(Instruction):
    """
        Push a new unbound REF cell onto the heap and copy it into that variable's register as
        well as an argument register.
    """

    def execute(self, wam):
        reg_idx, arg_idx = self.args
        wam.ensure_stack(reg_idx)
        wam.ensure_stack(arg_idx)
        h = len(wam.heap)
        wam.heap.append((REF, h))
        wam.reg_stack[reg_idx] = wam.heap[h]
        wam.reg_stack[arg_idx] = wam.heap[h]

class put_value(Instruction):
    """
        Copy a register into an argument register.
    """

    def execute(self, wam):
        reg_idx, arg_idx = self.args
        wam.ensure_stack(reg_idx)
        wam.ensure_stack(arg_idx)
        wam.reg_stack[arg_idx] = wam.reg_stack[reg_idx]

class get_variable(Instruction):
    """
        Copy an argument register into another register.
    """

    def execute(self, wam):
        reg_idx, arg_idx = self.args
        wam.ensure_stack(reg_idx)
        wam.ensure_stack(arg_idx)
        wam.reg_stack[reg_idx] = wam.reg_stack[arg_idx]

class get_value(Instruction):
    """
        Unify a register with an argument register.
    """

    def execute(self, wam):
        reg_idx, arg_idx = self.args
        wam.ensure_stack(reg_idx)
        wam.ensure_stack(arg_idx)
        reg_idx = wam.deref_reg(reg_idx)
        arg_idx = wam.deref_reg(arg_idx)
        wam.unify(reg_idx, arg_idx)

class WAM(object):
    def __init__(self):
        self.heap = []
        self.reg_stack = []
        self.mode = None
        self.next_subterm = None
        self.code = []
        self.p = 0
        self.labels = {}

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
            try:
                instr.execute(self)
            except:
                raise Exception('Exception while executing instruction: %s\nRegisters are: %s' % (instr, self.reg_stack))

    def load(self, functor, instrs):
        if functor is not None:
            self.labels[functor] = len(self.code)
        self.code.extend(instrs)

    def run(self):
        while self.p < len(self.code):
            instr = self.code[self.p]
            self.execute([instr])
            self.p += 1

class RegisterAllocation(object):
    def __init__(self):
        self.reg_allocation = {}
        self.next_register = 1

    def allocate_argument_registers(self, term):
        """
            Allocate registers for the arguments for this term.
        """
        if not isinstance(term, Compound):
            return
        for i, subterm in enumerate(term.subterms):
            arg_idx = i + 1
            if subterm in self.reg_allocation:
                return
            if not isinstance(subterm, Variable):
                self.reg_allocation[subterm] = arg_idx
        if self.next_register <= len(term.subterms):
            self.next_register = len(term.subterms) + 1

    def allocate_registers(self, term):
        """
            Allocate registers for a query or program term.

            >>> r = RegisterAllocation()
            >>> r.allocate_registers(Atom('a'))
            >>> r.reg_allocation
            {Atom('a'): 1}
            >>> x = Variable()
            >>> r.allocate_registers(x)
            >>> r.reg_allocation[x]
            2
            >>> t = Compound('f', x)
            >>> r.allocate_registers(t)
            >>> r.reg_allocation[t]
            3
        """
        def get_reg(term):
            if term not in self.reg_allocation:
                self.reg_allocation[term] = self.next_register
                self.next_register += 1
            return self.reg_allocation[term]

        if isinstance(term, (list, tuple)):
            subterms = term
        else:
            term = term.resolve()
            get_reg(term)
            if isinstance(term, Compound):
                subterms = term.subterms
            else:
                subterms = []

        # Immediate children are allocated registers
        for subterm in subterms:
            get_reg(subterm.resolve())

        # Then other descendants
        for subterm in subterms:
            subterm = subterm.resolve()
            self.allocate_registers(subterm)

    def __getitem__(self, item):
        return self.reg_allocation[item]

class Compiler(object):
    def compile_query(self, query, reg_allocation=None, vars_set=None, arg_idx=None):
        """
            >>> c = Compiler()
            >>> c.compile_query(Atom('a'))
            [put_structure(('a', 0), 1)]
            >>> c.compile_query(Variable())
            [set_variable(1)]
            >>> c.compile_query(Compound('f', Atom('a'), Variable()))
            [put_structure(('a', 0), 2), put_structure(('f', 2), 1), set_value(2), set_variable(3)]
            >>> Z = Variable()
            >>> W = Variable()
            >>> c.compile_query(Compound('p', Z, Compound('h', Z, W), Compound('f', W)))
            [put_structure(('h', 2), 3), set_variable(2), set_variable(5), put_structure(('f', 1), 4), set_value(5), put_structure(('p', 3), 1), set_value(2), set_value(3), set_value(4)]
        """

        if reg_allocation is None:
            reg_allocation = RegisterAllocation()

        if vars_set is None:
            vars_set = set()
            reg_allocation.allocate_registers(query)

        query = query.resolve()
        if isinstance(query, Atom):
            return [put_structure(query.get_functor(), reg_allocation[query])]
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
            instrs.append(put_structure(query.get_functor(), reg_allocation[query]))
            for subterm in query.subterms:
                subterm = subterm.resolve()
                if subterm in vars_set:
                    instrs.append(set_value(reg_allocation[subterm]))
                else:
                    vars_set.add(subterm)
                    instrs.append(set_variable(reg_allocation[subterm]))
            return instrs
        elif isinstance(query, Variable):
            if arg_idx is not None:
                if query in vars_set:
                    return [put_value(reg_allocation[query], arg_idx)]
                else:
                    vars_set.add(query)
                    return [put_variable(reg_allocation[query], arg_idx)]
            else:
                if query in vars_set:
                    return [set_value(reg_allocation[query])]
                else:
                    vars_set.add(query)
                    return [set_variable(reg_allocation[query])]

    def compile_query_m1(self, query, reg_allocation=None, vars_set=None):
        if isinstance(query, Atom):
            return [(call, query.get_functor())]
        elif isinstance(query, Compound):
            if reg_allocation is None:
                reg_allocation = RegisterAllocation()

            if vars_set is None:
                vars_set = set()
                reg_allocation.allocate_argument_registers(query)
                for subterm in query.subterms:
                    reg_allocation.allocate_registers(subterm)

            instrs = []
            for i, subterm in enumerate(query.subterms):
                subterm = subterm.resolve()
                instrs.extend(self.compile_query(subterm, reg_allocation, vars_set, arg_idx=(i+1)))
                vars_set.add(subterm)

            instrs.append(call(query.get_functor()))
            return instrs
        elif isinstance(query, Variable):
            raise Exception("Can't compile query for variable")

    def compile_program(self, program, reg_allocation=None, vars_set=None, arg_idx=None):
        """
            >>> c = Compiler()
            >>> c.compile_program(Atom('a'))
            [get_structure(('a', 0), 1)]
            >>> c.compile_program(Variable())
            [unify_variable(1)]
            >>> c.compile_program(Compound('f', Atom('a'), Variable()))
            [get_structure(('f', 2), 1), unify_variable(2), unify_variable(3), get_structure(('a', 0), 2)]
            >>> X = Variable()
            >>> Y = Variable()
            >>> c.compile_program(Compound('p', Compound('f', X), Compound('h', Y, Compound('f', Atom('a'))), Y))
            [get_structure(('p', 3), 1), unify_variable(2), unify_variable(3), unify_variable(4), get_structure(('f', 1), 2), unify_variable(5), get_structure(('h', 2), 3), unify_value(4), unify_variable(6), get_structure(('f', 1), 6), unify_variable(7), get_structure(('a', 0), 7)]
        """

        if reg_allocation is None:
            reg_allocation = RegisterAllocation()

        if vars_set is None:
            vars_set = set()
            reg_allocation.allocate_registers(program)

        program = program.resolve()
        if isinstance(program, Atom):
            return [get_structure(program.get_functor(), reg_allocation[program])]
        elif isinstance(program, Compound):
            instrs = []
            # Build this term
            instrs.append(get_structure(program.get_functor(), reg_allocation[program]))
            for subterm in program.subterms:
                subterm = subterm.resolve()
                if subterm in vars_set:
                    instrs.append(unify_value(reg_allocation[subterm]))
                else:
                    vars_set.add(subterm)
                    instrs.append(unify_variable(reg_allocation[subterm]))
            # Build nested terms
            for subterm in program.subterms:
                subterm = subterm.resolve()
                if isinstance(subterm, Variable):
                    continue
                instrs.extend(self.compile_program(subterm, reg_allocation, vars_set))
                vars_set.add(subterm)
            return instrs
        elif isinstance(program, Variable):
            if arg_idx is not None:
                if program in vars_set:
                    return [get_value(reg_allocation[program], arg_idx)]
                else:
                    vars_set.add(program)
                    return [get_variable(reg_allocation[program], arg_idx)]
            else:
                if program in vars_set:
                    return [unify_value( reg_allocation[program])]
                else:
                    vars_set.add(program)
                    return [unify_variable( reg_allocation[program])]

    def compile_program_m1(self, program, reg_allocation=None, vars_set=None):
        if isinstance(program, Atom):
            return [(proceed,)]
        elif isinstance(program, Compound):
            if reg_allocation is None:
                reg_allocation = RegisterAllocation()

            if vars_set is None:
                vars_set = set()
                reg_allocation.allocate_argument_registers(program)
                for subterm in program.subterms:
                    reg_allocation.allocate_registers(subterm)

            instrs = []
            for i, subterm in enumerate(program.subterms):
                subterm = subterm.resolve()
                instrs.extend(self.compile_program(subterm, reg_allocation, vars_set, arg_idx=(i+1)))
                vars_set.add(subterm)

            instrs.append(proceed())
            return instrs
        elif isinstance(program, Variable):
            raise Exception("Can't compile program for variable")

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
        name = instr.get_name()
        args = instr.get_args()
        if len(args) == 0:
            print name
        else:
            print '%s %s' % (name, ', '.join(arg_str(x) for x in args))

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
    query_instrs = compiler.compile_query_m1(query, query_reg_map)
    print_instrs(query_instrs)
    print 'Register allocations are: ', ', '.join('%s: %s' % (n, query_reg_map[v]) for n,v in query_scope.names_to_vars.items())

    print
    print 'Compiled program to:'
    program_reg_map = {}
    program_instrs = compiler.compile_program_m1(program, program_reg_map)
    print_instrs(program_instrs)
    print 'Register allocations are: ', ', '.join('%s: %s' % (n, program_reg_map[v]) for n,v in program_scope.names_to_vars.items())

    print
    print 'Running query and program...'
    wam.load(None, query_instrs)
    wam.load(program.get_functor(), program_instrs)
    wam.run()
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
