import sys

from term import *
from term_parser import *

class Enum(object):
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        return self.name

def enums(s):
    return [Enum(w) for w in s.split()]

REF, STR = enums('REF STR')
READ, WRITE = enums('READ WRITE')

#TODO - find a better way to segregate permanent and temporary registers!
PERMANENT_REGISTER_BASE = 1000

PROLOG_OPS = {
    ':-': (1200, 'xfx'),
    ',': (1000, 'xfy')
}

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

    def execute(self, wam):
        f = getattr(self, self.__class__.__name__)
        f(wam, *self.args)

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

    def put_structure(self, wam, functor, reg_idx):
        h = wam.add_to_heap((STR, ), functor)
        wam.set_reg(reg_idx, (REF, h))

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

    def set_variable(self, wam, reg_idx):
        h = wam.add_to_heap((REF,))
        wam.set_reg(reg_idx, wam.heap[h])

class set_value(Instruction):
    """
        Push a new cell onto the heap and copy into it the register's value.

        >>> w = WAM()
        >>> w.reg_stack = [(REF, 0)]
        >>> set_value(0).execute(w)
        >>> w.heap
        [(REF, 0)]
    """

    def set_value(self, wam, reg_idx):
        wam.add_to_heap(wam.get_reg(reg_idx))

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

    def get_structure(self, wam, functor, reg_idx):
        wam.next_subterm = 1
        idx = wam.deref_reg(reg_idx)
        if idx is not None:
            a, b = wam.heap[idx]
        else:
            a, b = wam.get_reg(reg_idx)
        if a is REF:
            h = wam.add_to_heap((STR,), functor)
            wam.bind(idx, h)
            wam.mode = WRITE
        elif a is STR and wam.heap[b] == functor:
            wam.next_subterm = b + 1
            wam.mode = READ
        else:
            assert a is REF or a is STR, 'Cell pointed to by register %d was %s' % (reg_idx, (a, b))
            wam.backtrack()

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

    def unify_variable(self, wam, reg_idx):
        if wam.mode == READ:
            wam.set_reg(reg_idx, (REF, wam.next_subterm))
        elif wam.mode == WRITE:
            h = wam.add_to_heap((REF, ))
            wam.set_reg(reg_idx, wam.heap[h])
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

    def unify_value(self, wam, reg_idx):
        if wam.mode == READ:
            idx = wam.deref_reg(reg_idx)
            assert idx is not None
            if not wam.unify(idx, wam.next_subterm):
                wam.backtrack()
                return
        elif wam.mode == WRITE:
            wam.add_to_heap(wam.get_reg(reg_idx))
        else:
            raise Exception('Mode not set!')
        wam.next_subterm += 1

class call(Instruction):
    def call(self, wam, functor):
        if functor not in wam.labels:
            wam.backtrack()
            return
        wam.cp = wam.p + 1
        wam.p = wam.labels[functor] - 1  # -1 because p will be incremented after this instruction
        #wam.reg_stack = wam.reg_stack[:functor[1]+1]
        wam.num_args = functor[1]

class proceed(Instruction):
    def proceed(self, wam):
        if wam.cp is not None:
            wam.p = wam.cp - 1
        wam.cp = None

class put_variable(Instruction):
    """
        Push a new unbound REF cell onto the heap and copy it into that variable's register as
        well as an argument register.
    """

    def put_variable(self, wam, reg_idx, arg_idx):
        h = wam.add_to_heap((REF,))
        wam.set_reg(reg_idx, wam.heap[h])
        wam.set_reg(arg_idx, wam.heap[h])

class put_value(Instruction):
    """
        Copy a register into an argument register.
    """

    def put_value(self, wam, reg_idx, arg_idx):
        wam.set_reg(arg_idx, wam.get_reg(reg_idx))

class get_variable(Instruction):
    """
        Copy an argument register into another register.
    """

    def get_variable(self, wam, reg_idx, arg_idx):
        wam.set_reg(reg_idx, wam.get_reg(arg_idx))

class get_value(Instruction):
    """
        Unify a register with an argument register.
    """

    def get_value(self, wam, reg_idx, arg_idx):
        reg_idx = wam.deref_reg(reg_idx)
        arg_idx = wam.deref_reg(arg_idx)
        if not wam.unify(reg_idx, arg_idx):
            wam.backtrack()

class allocate(Instruction):
    def allocate(self, wam, size):
        wam.push_frame(EnvironmentFrame(wam.e, wam.cp, size))

class deallocate(Instruction):
    def deallocate(self, wam):
        wam.p = wam.stack[wam.e].cp - 1
        wam.pop_frame(wam.e)

class label(Instruction):
    def label(self, wam, name):
        pass

class try_me_else(Instruction):
    def try_me_else(self, wam, label):
        label_pos = wam.find_label(label, wam.p)
        wam.hb = len(wam.heap)
        wam.push_frame(ChoicePoint(wam.num_args, wam.reg_stack[:wam.num_args+1], wam.e, wam.cp, wam.b, label_pos, len(wam.trail), wam.hb))

class retry_me_else(Instruction):
    def retry_me_else(self, wam, label):
        choice_point = wam.stack[wam.b]
        wam.reg_stack[:choice_point.num_args + 1] = choice_point.args
        wam.e = choice_point.ce
        wam.cp = choice_point.cp
        choice_point.bp = wam.find_label(label, wam.p)
        wam.unwind_trail(choice_point.tr)
        wam.heap = wam.heap[:choice_point.h]
        wam.hb = choice_point.h

class trust_me(Instruction):
    def trust_me(self, wam):
        choice_point = wam.stack[wam.b]
        wam.reg_stack[:choice_point.num_args + 1] = choice_point.args
        wam.e = choice_point.ce
        wam.cp = choice_point.cp
        wam.unwind_trail(choice_point.tr)
        wam.heap = wam.heap[:choice_point.h]
        wam.hb = choice_point.h
        wam.pop_frame(wam.b)

class Frame(object):
    def __init__(self):
        self.position = None

class EnvironmentFrame(Frame):
    def __init__(self, ce, cp, size):
        self.ce = ce
        self.cp = cp
        self.reg_stack = [None] * (size+1)

    def __str__(self):
        return 'ce = %s   cp = %s   reg_stack = [%s]' % (self.ce, self.cp, ', '.join(str(x) for x in self.reg_stack[1:]))

class ChoicePoint(Frame):
    def __init__(self, num_args, args, ce, cp, b, bp, tr, h):
        self.num_args = num_args
        self.args = args
        self.ce = ce
        self.cp = cp
        self.b = b
        self.bp = bp
        self.tr = tr
        self.h = h

    def __str__(self):
        return 'num_args = %d    args = [%s]   ce = %s   cp = %s   b = %s   bp = %s   tr = %s   h = %s' \
               % (self.num_args, ', '.join(str(x) for x in self.args[1:]), self.ce, self.cp, self.b, self.bp, self.tr, self.h)

class WAM(object):
    def __init__(self):
        self.heap = []
        self.hb = 0
        self.reg_stack = []
        self.mode = None
        self.next_subterm = None
        self.code = []
        self.p = 0
        self.cp = None
        self.labels = {}
        self.stack = []
        self.e = None
        self.b = None
        self.trail = []
        self.num_args = None

    def add_to_heap(self, *items):
        rv = len(self.heap)
        for i, item in enumerate(items):
            if item == (STR,):
                item = (STR, rv + i + 1)
            elif item == (REF,):
                item = (REF, rv + i)
            self.heap.append(item)
        return rv

    def push_frame(self, frame):
        frame.position = len(self.stack)
        self.stack.append(frame)
        if isinstance(frame, EnvironmentFrame):
            self.e = frame.position
        if isinstance(frame, ChoicePoint):
            self.b = frame.position
        print '(pushed %s frame at position %d)' % (type(frame), frame.position)

    def pop_frame(self, frame_idx):
        frame = self.stack[frame_idx]
        if isinstance(frame, EnvironmentFrame):
            self.e = frame.ce
        if isinstance(frame, ChoicePoint):
            self.b = frame.b
        self.stack = self.stack[:max(self.e, self.b, -1)+1]
        print '(popped %s frame at %d)' % (type(frame), frame_idx)

    def backtrack(self):
        if self.b is None:
            raise Exception('Cannot backtrack any more; exhausted all choice points')
        assert isinstance(self.stack[self.b], ChoicePoint)
        self.p = self.stack[self.b].bp - 1

    def find_label(self, label_name, pos):
        """
            Search for the first matching label after the code position.
        """
        for i in range(pos, len(self.code)):
            instr = self.code[i]
            if isinstance(instr, label) and instr.get_args()[0] == label_name:
                return i

        return None

    def ensure_stack(self, idx):
        if idx < PERMANENT_REGISTER_BASE:
            if len(self.reg_stack) <= idx:
                extra = idx - len(self.reg_stack) + 1
                self.reg_stack.extend((None, None) for i in range(extra))

    def set_reg(self, idx, value):
        if idx < PERMANENT_REGISTER_BASE:
            self.ensure_stack(idx)
            self.reg_stack[idx] = value
        else:
            self.stack[self.e].reg_stack[idx - PERMANENT_REGISTER_BASE] = value

    def get_reg(self, idx):
        if idx < PERMANENT_REGISTER_BASE:
            self.ensure_stack(idx)
            return self.reg_stack[idx]
        else:
            return self.stack[self.e].reg_stack[idx - PERMANENT_REGISTER_BASE]

    def deref(self, idx):
        a, b = self.heap[idx]
        while a is REF and b != idx:
            idx = b
            a, b = self.heap[idx]
        return idx

    def deref_reg(self, reg_idx):
        a, b = self.get_reg(reg_idx)
        if a is REF:
            return self.deref(b)
        return None

    def record_trail(self, idx):
        if idx < self.hb:   # or (self.h < idx and idx < self.b)
            self.trail.append(idx)

    def unwind_trail(self, unwind_to):
        while len(self.trail) > unwind_to:
            idx = self.trail.pop()
            self.heap[idx] = (REF, idx)

    def bind(self, idx1, idx2):
        """
            Bind a variable at idx1 to idx2.  If we have a choice (i.e. if both are currently unbound)
            we bind the higher address to the lower address.

            >>> wam = WAM()
            >>> wam.hb = 2
            >>> wam.heap = [(REF, 0), (REF, 1)]
            >>> wam.bind(0, 1)
            >>> wam.heap
            [(REF, 0), (REF, 0)]
            >>> wam.trail
            [1]

            >>> wam.trail = []
            >>> wam.heap = [(REF, 0), (REF, 1)]
            >>> wam.bind(1, 0)
            >>> wam.heap
            [(REF, 0), (REF, 0)]
            >>> wam.trail
            [1]

            >>> wam.trail = []
            >>> wam.heap = [(REF, 0), (STR, 2)]
            >>> wam.bind(0, 1)
            >>> wam.heap
            [(REF, 1), (STR, 2)]
            >>> wam.trail
            [0]

            >>> wam.trail = []
            >>> wam.heap = [(STR, 2), (REF, 1)]
            >>> wam.bind(0, 1)
            >>> wam.heap
            [(STR, 2), (REF, 0)]
            >>> wam.trail
            [1]
        """
        if idx1 < idx2:
            idx1, idx2 = idx2, idx1
        if self.heap[idx1] != (REF, idx1):
            idx1,idx2 = idx2,idx1
        assert self.heap[idx1] == (REF, idx1)
        self.heap[idx1] = (REF, idx2)
        self.record_trail(idx1)

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
            #try:
                instr.execute(self)
            #except Exception, ex:
            #    raise Exception('Exception while executing instruction: %s\nRegisters are: %s\nFrame is: %s\n%s' % (instr, self.reg_stack, self.stack[self.e].reg_stack, ex))

    def load(self, functor, instrs):
        start = len(self.code)
        if functor is not None:
            self.labels[functor] = start
        self.code.extend(instrs)
        return start

    def run(self):
        while self.p < len(self.code):
            instr = self.code[self.p]
            print '*', self.p, instr
            self.execute([instr])
            self.p += 1
            #print_wam(self)

class RegisterAllocation(object):
    def __init__(self):
        self.reg_allocation = {}
        self.next_register = 1
        self.permanent_allocation = {}
        self.next_permanent_register = 1
        self.permanent_variables = set()

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
        def ensure_allocated(term):
            if term not in self.reg_allocation and term not in self.permanent_allocation:
                if term in self.permanent_variables:
                    self.allocate_permanent_register(term)
                else:
                    self.allocate_register(term)

        if isinstance(term, (list, tuple)):
            subterms = term
        else:
            term = term.resolve()
            ensure_allocated(term)
            if isinstance(term, Compound):
                subterms = term.subterms
            else:
                subterms = []

        # Immediate children are allocated registers
        for subterm in subterms:
            ensure_allocated(subterm.resolve())

        # Then other descendants
        for subterm in subterms:
            subterm = subterm.resolve()
            self.allocate_registers(subterm)

    def find_permanent_variables(self, head, subgoals, threshold=2):
        if len(subgoals) < 1:
            return
        # The head atom is considered to be part of the first body goal.
        subsets = []
        if head is not None:
            subsets.append(Compound(':-', head, subgoals[0]))
        else:
            subsets.append(subgoals[0])
        for i in range(1, len(subgoals)):
            subsets.append(subgoals[i])

        # Count how many subsets each variable appears in.
        var_counts = {}
        for subset in subsets:
            for v in find_variables(subset):
                if v in var_counts:
                    var_counts[v] += 1
                else:
                    var_counts[v] = 1

        # All those variables that appeared in more than one subterm are permanent
        for var, count in var_counts.items():
            if count >= threshold:
                self.permanent_variables.add(var)

    def allocate_register(self, term):
        assert term not in self.reg_allocation
        assert term not in self.permanent_allocation
        self.reg_allocation[term] = self.next_register
        self.next_register += 1

    def allocate_permanent_register(self, term):
        assert term not in self.reg_allocation
        assert term not in self.permanent_allocation
        self.permanent_allocation[term] = self.next_permanent_register
        self.next_permanent_register += 1

    def __getitem__(self, item):
        if item in self.reg_allocation:
            return self.reg_allocation[item]
        else:
            return PERMANENT_REGISTER_BASE + self.permanent_allocation[item]

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

    def compile_query_m2(self, query, reg_allocation=None):
        # A query must put all its variables in permanent registers, so their values can be recovered
        subgoals = find_subgoals(query)
        reg_allocation.find_permanent_variables(None, subgoals, threshold=1)
        vars_set = set()
        instrs = []
        for sg in subgoals:
            instrs.extend(self.compile_query_m1(sg, reg_allocation, vars_set))
        return instrs

    def compile_program(self, program, reg_allocation=None, vars_set=None, arg_idx=None, recurse=True):
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
            if recurse:
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
        """
            >>> c = Compiler()
            >>> X = Variable()
            >>> c.compile_program_m1(Compound('f', Compound('g', Compound('g', X)), X))
            [get_structure(('g', 1), 1), unify_variable(3), get_variable(4, 2), get_structure(('g', 1), 3), unify_value(4), proceed()]
        """
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

            # First do basic structure for all subterms
            for i, subterm in enumerate(program.subterms):
                subterm = subterm.resolve()
                instrs.extend(self.compile_program(subterm, reg_allocation, vars_set, arg_idx=(i+1), recurse=False))
                vars_set.add(subterm)

            # Then do remaining structure for any subterms that need it
            for subterm in program.subterms:
                subterm = subterm.resolve()
                if not isinstance(subterm, Compound):
                    continue

                for subterm in subterm.subterms:
                    subterm = subterm.resolve()
                    if isinstance(subterm, Variable):
                        continue
                    instrs.extend(self.compile_program(subterm, reg_allocation, vars_set))
                    vars_set.add(subterm)

            instrs.append(proceed())
            return instrs
        elif isinstance(program, Variable):
            raise Exception("Can't compile program for variable")

    def allocate_rule_registers(self, head, subgoals, reg_allocation):
        reg_allocation.find_permanent_variables(head, subgoals)

        reg_allocation.allocate_argument_registers(head)
        for sg in subgoals:
            reg_allocation.allocate_argument_registers(sg)

        reg_allocation.allocate_registers(head.subterms)
        for sg in subgoals:
            reg_allocation.allocate_registers(sg.subterms)
        return reg_allocation

    def compile_rule(self, head, subgoals, reg_allocation=None):
        if reg_allocation is None:
            reg_allocation = RegisterAllocation()
        reg_allocation = self.allocate_rule_registers(head, subgoals, reg_allocation)
        vars_set = set()
        instrs = []
        if len(subgoals) > 0:
            instrs.append(allocate(len(reg_allocation.permanent_allocation)))
        instrs.extend(self.compile_program_m1(head, reg_allocation, vars_set)[:-1])  # Remove trailing proceed instruction
        for sg in subgoals:
            instrs.extend(self.compile_query_m1(sg, reg_allocation, vars_set))
        if len(subgoals) > 0:
            instrs.append(deallocate())
        else:
            instrs.append(proceed())
        return instrs

    def compile_predicate(self, rules):
        if len(rules) == 0:
            raise Exception('Predicate needs at least one clause')

        heads_and_subgoals = [(get_head(x), get_body_subgoals(x)) for x in rules]
        functors = [x.get_functor() for x,_ in heads_and_subgoals]

        distinct_functors = set(functors)
        if len(distinct_functors) > 1:
            raise Exception('Predicate needs a distinct functor (has %s)' % ', '.join(format_functor(x) for x in distinct_functors))
        functor = functors[0]

        instrs = []
        instrs.append(label(format_functor(functor)))
        for i, (head, subgoals) in enumerate(heads_and_subgoals):
            if i > 0:
                instrs.append(label('L%d' % i))
            if len(rules) > 1:
                if i == 0:
                    instrs.append(try_me_else('L1'))
                elif i < len(rules) - 1:
                    instrs.append(retry_me_else('L%d' % (i+1)))
                else:
                    instrs.append(trust_me())
            instrs.extend(self.compile_rule(head, subgoals))

        return instrs

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
            h = wam.add_to_heap((STR,), term.get_functor())
        elif isinstance(term, Variable):
            if term in var_idxes:
                h = var_idxes[term]
                wam.add_to_heap((REF, h))
            else:
                h = wam.add_to_heap((REF,))
                var_idxes[term] = h
        elif isinstance(term, Compound):
            sub_idxes = [self.write_to_heap(st, wam, var_idxes) for st in term.subterms]
            h = wam.add_to_heap((STR,), term.get_functor())
            for si in sub_idxes:
                wam.add_to_heap((REF, si))
        else:
            raise Exception('Unhandled term type: %s' % type(term))
        return h

def print_instrs(instrs, offset=0):
    def arg_str(arg):
        if type(arg) is tuple and type(arg[0]) is str and type(arg[1]) is int:
            return '%s/%d' % arg
        return str(arg)

    for i, instr in enumerate(instrs):
        name = instr.get_name()
        args = instr.get_args()
        if isinstance(instr, label):
            print '%s:' % (args)
        elif len(args) == 0:
            print '[%2d] %s' % (i + offset, name)
        else:
            print '[%2d] %s %s' % (i + offset, name, ', '.join(arg_str(x) for x in args))

def print_heap(heap):
    print '       ',
    for i in range(10):
        print '[%2d]    ' % i,
    print
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

def print_wam(wam):
    print 'WAM state:'
    print 'mode = %s   next = %s' % (wam.mode, wam.next_subterm)
    print 'p = %d   cp = %s' % (wam.p, wam.cp)
    print 'e = %s   b = %s' % (wam.e, wam.b)
    print 'hb = %d   trail = %s' % (wam.hb, wam.trail)
    print 'Heap:'
    print_heap(wam.heap)
    print 'Registers:'
    print_heap(wam.reg_stack)
    print 'Stack:'
    for i, frame in enumerate(wam.stack):
        print '[%2d]   %s' % (i, frame)
    #print 'Code:'
    #print_instrs(wam.code)
    print

def main():
    try:
        if len(sys.argv) < 2:
            raise IndexError
        program_strs = sys.argv[1:-1]
        query_str = sys.argv[-1]
        programs_and_scopes = [parse(PROLOG_OPS, x) for x in program_strs]
        query, query_scope = parse(PROLOG_OPS, query_str)
    except SyntaxError, ex:
        print ex
        sys.exit(1)
    except IndexError:
        print 'Please enter a program (one or more rules) and a query'
        print '(you will probably need quotes around each item)'
        print 'E.g.   wam.py   "p(X, Y) :- q(X, Z), r(Z, Y)" "q(a, b)" "r(b, c)" "p(U, V)"'
        sys.exit(1)

    print 'Running query:    %s' % unparse(PROLOG_OPS, query, query_scope)
    print 'Against program:'
    for ps in programs_and_scopes:
        print '    %s' % unparse(PROLOG_OPS, *ps)

    compiler = Compiler()
    wam = WAM()

    predicates = {}
    for p,_ in programs_and_scopes:
        functor = get_head(p).get_functor()
        if functor not in predicates:
            predicates[functor] = []
        predicates[functor].append(p)

    for functor, rules in predicates.items():
        pred_instrs = compiler.compile_predicate(rules)
        wam.load(functor, pred_instrs)

    print
    print 'Compiled program to:'
    print_instrs(wam.code)

    query_reg_allocation = RegisterAllocation()
    query_instrs = compiler.compile_query_m2(query, reg_allocation=query_reg_allocation)
    wam.p = wam.load(None, query_instrs)
    print
    print 'Compiled query to:'
    print_instrs(wam.code[wam.p:], offset=wam.p)
    print 'Register allocations are: ', ', '.join('%s: %s' % (n, query_reg_allocation[v]) for n,v in query_scope.names_to_vars.items())

    print
    print 'Running query and program...'

    wam.push_frame(EnvironmentFrame(None, None, size=len(query_reg_allocation.permanent_allocation)))
    wam.run()
    for n, v in query_scope.names_to_vars.items():
        print '%s = %s' % (n, wam.get_term_repr(wam.deref_reg(query_reg_allocation[v])))

    print
    print 'Final WAM state:'
    print_wam(wam)

if __name__ == '__main__':
    main()
