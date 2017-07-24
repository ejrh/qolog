import unittest

from wam import *

class M0Test(unittest.TestCase):

    # Figure 2.3: Compiled code for L_0 query ?- p(Z, h(Z, W), f(W)).
    fig_2_3_instrs = [
        put_structure(('h', 2), 3),   # ?- X3 = h
        set_variable(2),              #          (Z,
        set_variable(5),              #             W),
        put_structure(('f', 1), 4),   #    X4 = f
        set_value(5),                 #          (W),
        put_structure(('p', 3), 1),   #    X1 = p
        set_value(2),                 #          (Z,
        set_value(3),                 #             X3,
        set_value(4)                  #                X4).
    ]

    # Figure 2.4: Compiled code for L_0 program p(f(X), h(Y, f(a)), Y).
    fig_2_4_instrs = [
        get_structure(('p', 3), 1),   # X1 = p
        unify_variable(2),            #       (X2,
        unify_variable(3),            #           X3,
        unify_variable(4),            #              Y),
        get_structure(('f', 1), 2),   # X2 = f
        unify_variable(5),            #       (X),
        get_structure(('h', 2), 3),   # X3 = h
        unify_value(4),               #       (Y,
        unify_variable(6),            #          X6),
        get_structure(('f', 1), 6),   # X6 = f
        unify_variable(7),            #       (X7),
        get_structure(('a', 0), 7)    # X7 = a.
    ]

    def test_fig_2_3(self):
        compiler = Compiler()

        Z = Variable()
        W = Variable()
        query = Compound('p', Z, Compound('h', Z, W), Compound('f', W))
        instrs = compiler.compile_query(query)
        self.assertEqual(instrs, self.fig_2_3_instrs)

    def test_fig_2_4(self):
        compiler = Compiler()

        X = Variable()
        Y = Variable()
        program = Compound('p', Compound('f', X), Compound('h', Y, Compound('f', Atom('a'))), Y)
        instrs = compiler.compile_program(program)
        self.assertEqual(instrs, self.fig_2_4_instrs)

    def test_ex_2_1(self):
        """
            Exercise 2.1

            Verify that the effect of executing the sequence of instructions shown in Figure 2.3
            (starting with H = 0) does indeed yield a correct heap representation for the term
            p(Z, h(Z,W), f(W)) -- the one shown earlier as Figure 2.1, in fact.
        """

        wam = WAM()
        wam.execute(self.fig_2_3_instrs)
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
        wam.execute(self.fig_2_3_instrs)
        aW = wam.deref_reg(5)
        aZ = wam.deref_reg(2)
        wam.execute(self.fig_2_4_instrs)
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
            put_structure( ('f', 1), 2),
            set_variable(5),
            put_structure(('a', 0), 7),
            put_structure(('f', 1), 6),
            set_value(7),
            put_structure(('h', 2), 3),
            set_variable(4),
            set_value(6),
            put_structure(('p', 3), 1),
            set_value(2),
            set_value(3),
            set_value(4)
        ])

        W = Variable()
        Z = Variable()
        program = Compound('p', Z, Compound('h', Z, W), Compound('f', W))
        instrs = compiler.compile_program(program)
        self.assertEqual(instrs, [
            get_structure(('p', 3), 1),
            unify_variable(2),
            unify_variable(3),
            unify_variable(4),
            get_structure(('h', 2), 3),
            unify_value(2),
            unify_variable(5),
            get_structure(('f', 1), 4),
            unify_value(5)
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
        query_reg_allocation = RegisterAllocation()
        query_instrs = compiler.compile_query(query, query_reg_allocation)

        W = Variable()
        Z = Variable()
        program = Compound('p', Z, Compound('h', Z, W), Compound('f', W))
        program_reg_allocation = RegisterAllocation()
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


class M1Test(unittest.TestCase):
    # Figure 2.9: Argument registers for L_1 query ?- p(Z, h(Z, W), f(W)).
    fig_2_9_instrs = [
        put_variable(4, 1),           # ?- p(Z,
        put_structure(('h', 2), 2),   #        h
        set_value(4),                 #         (Z,
        set_variable(5),              #            W),
        put_structure(('f', 1), 3),   #               f
        set_value(5),                 #                (W)
        call(('p', 3))                #                   ).
    ]

    # ?- p(f(X), h(Y, f(a)), Y).
    ex9_query = [
        put_structure(('f', 1), 1),
        set_variable(4),
        put_structure(('a', 0), 7),
        put_structure(('f', 1), 6),
        set_value(7),
        put_structure(('h', 2), 2),
        set_variable(5),
        set_value(6),
        put_value(5, 3),
        call(('p', 3))
    ]

    # Figure 2.10: Argument registers for L_1 fact p(f(X), h(Y, f(a)), Y).
    fig_2_10_instrs = [
        get_structure(('f', 1), 1),   # p(f
        unify_variable(4),            #    (X),
        get_structure(('h', 2), 2),   #        h
        unify_variable(5),            #         (Y,
        unify_variable(6),            #            X6),
        get_value(5, 3),              #                Y),
        get_structure(('f', 1), 6),   # X6 = f
        unify_variable(7),            #        (X7),
        get_structure(('a', 0), 7),   # X7 = a
        proceed()                     # .
    ]

    ex9_program = [
        get_variable(4, 1),
        get_structure(('h', 2), 2),
        unify_value(4),
        unify_variable(5),
        get_structure(('f', 1), 3),
        unify_value(5),
        proceed()
    ]

    def test_fig_2_9(self):
        compiler = Compiler()

        Z = Variable()
        W = Variable()
        query = Compound('p', Z, Compound('h', Z, W), Compound('f', W))
        instrs = compiler.compile_query_m1(query)
        self.assertEqual(instrs, self.fig_2_9_instrs)

    def test_fig_2_10(self):
        compiler = Compiler()

        X = Variable()
        Y = Variable()
        program = Compound('p', Compound('f', X), Compound('h', Y, Compound('f', Atom('a'))), Y)
        instrs = compiler.compile_program_m1(program)
        self.assertEqual(instrs, self.fig_2_10_instrs)

    def test_ex_2_6(self):
        """
            Exercise 2.6

            Verify that the effect of executing the sequence of M_1 instructions shown in
            Figure 2.9 produces the same heap representation as that produced by the M_0 code of
            Figure 2.3 (see Exercise 2.1).
        """

        wam = WAM()
        wam.execute(self.fig_2_9_instrs[:-1])   # last instruction is call; remove it
        self.assertEqual(wam.get_term_repr(wam.deref_reg(1)), '_G0')
        self.assertEqual(wam.get_term_repr(wam.deref_reg(2)), 'h(_G0, _G4)')
        self.assertEqual(wam.get_term_repr(wam.deref_reg(3)), 'f(_G4)')

    def test_ex_2_7(self):
        """
            Exercise 2.7

            Verify that the effect of executing the sequence of M_1 instructions shown in
            Figure 2.10 right after that in Figure 2.9 produces the MGU of the terms
            p(Z, h(Z, W), f(W)) and p(f(X), h(Y, f(a)), Y).  That is, the binding
            W = f(a), X = f(a), Y = f(f(a)), Z = f(f(a)).
        """

        wam = WAM()
        wam.execute(self.fig_2_9_instrs[:-1])   # last instruction is call; remove it
        wam.execute(self.fig_2_10_instrs)
        aW = wam.deref_reg(4)
        aX = wam.deref_reg(4)
        aY = wam.deref_reg(5)
        aZ = wam.deref_reg(1)
        self.assertEqual(wam.get_term_repr(aW), 'f(a)')
        self.assertEqual(wam.get_term_repr(aX), 'f(a)')
        self.assertEqual(wam.get_term_repr(aY), 'f(f(a))')
        self.assertEqual(wam.get_term_repr(aZ), 'f(f(a))')

    def test_ex_2_8(self):
        """
            Exercise 2.8

            What are the respective sequences of M_1 instructions for L_1 query term
            ?- p(f(X), h(Y, f(a)), Y) and L_1 program term p(Z, h(Z, W), f(W)) ?
        """

        compiler = Compiler()

        X = Variable()
        Y = Variable()
        query = Compound('p', Compound('f', X), Compound('h', Y, Compound('f', Atom('a'))), Y)
        instrs = compiler.compile_query_m1(query)
        self.assertEqual(instrs, [
            put_structure(('f', 1), 1),
            set_variable(4),
            put_structure(('a', 0), 7),
            put_structure(('f', 1), 6),
            set_value(7),
            put_structure(('h', 2), 2),
            set_variable(5),
            set_value(6),
            put_value(5, 3),
            call(('p', 3))
        ])

        W = Variable()
        Z = Variable()
        program = Compound('p', Z, Compound('h', Z, W), Compound('f', W))
        instrs = compiler.compile_program_m1(program)
        self.assertEqual(instrs, [
            get_variable(4, 1),
            get_structure(('h', 2), 2),
            unify_value(4),
            unify_variable(5),
            get_structure(('f', 1), 3),
            unify_value(5),
            proceed()
        ])

    def test_ex_2_9(self):
        """
            Exercise 2.9

            After doing Exercise 2.8, verify that the effect of executing the sequence you
            produced yields the same solution as that of Exercise 2.7.
        """

        compiler = Compiler()

        X = Variable()
        Y = Variable()
        query = Compound('p', Compound('f', X), Compound('h', Y, Compound('f', Atom('a'))), Y)
        query_reg_allocation = RegisterAllocation()
        query_instrs = compiler.compile_query_m1(query, query_reg_allocation)

        W = Variable()
        Z = Variable()
        program = Compound('p', Z, Compound('h', Z, W), Compound('f', W))
        # Because there is a shared register space, we reuse the query's register allocation to
        # force the program's registers into different slots.
        program_reg_allocation = query_reg_allocation   # RegisterAllocation()
        program_instrs = compiler.compile_program_m1(program, program_reg_allocation)

        wam = WAM()
        wam.load(None, query_instrs)
        wam.load(program.get_functor(), program_instrs)
        wam.run()

        aW = wam.deref_reg(program_reg_allocation[W])
        aX = wam.deref_reg(query_reg_allocation[X])
        aY = wam.deref_reg(query_reg_allocation[Y])
        aZ = wam.deref_reg(program_reg_allocation[Z])

        #print 'X reg:', query_reg_allocation.reg_allocation[X], 'X addr:', aX, 'X: ', wam.get_term_repr(aX)
        #print 'Y reg:', query_reg_allocation.reg_allocation[Y], 'Y addr:', aY, 'Y: ', wam.get_term_repr(aY)
        #print 'Z reg:', program_reg_allocation.reg_allocation[Z], 'Z addr:', aZ, 'Z: ', wam.get_term_repr(aZ)
        #print 'W reg:', program_reg_allocation.reg_allocation[W], 'W addr:', aW, 'W: ', wam.get_term_repr(aW)
        self.assertEqual(wam.get_term_repr(aW), 'f(a)')
        self.assertEqual(wam.get_term_repr(aX), 'f(a)')
        self.assertEqual(wam.get_term_repr(aY), 'f(f(a))')
        self.assertEqual(wam.get_term_repr(aZ), 'f(f(a))')
