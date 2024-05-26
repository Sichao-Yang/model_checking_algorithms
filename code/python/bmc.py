from z3 import Solver, Bool, substitute, Not, sat, unsat, simplify
import copy


class BMC:
    def __init__(self, inputs, primed_inputs, vars, primed_vars, init, trans, post, filename):
        """
        :param inputs:
        :param vars: Boolean Variables
        :param primed_vars: The Post Condition Variable
        :param init: The initial State
        :param trans: Transition Function
        :param post: The Safety Property
        """
        self.vars = vars + inputs
        self.primed_vars = primed_vars + primed_inputs
        self.init = init
        self.trans = trans
        self.post = post
        self.filename = filename
        self.frames = list()
        # because bmc unrolls every single iteration, the variables are increasing,
        # therefore, we dont need to create lMap or primeMap
        self.vardict = dict()

    def vardef(self, n: str):
        if n in self.vardict:
            return self.vardict[n]
        v = Bool(n)
        self.vardict[n] = v
        return v

    def setup(self, induction=False):
        self.slv = Solver()
        initmap = [(self.vars[i], self.vardef(str(self.vars[i]) + "_0")) for i in range(len(self.vars))]
        if not induction:
            self.slv.add(substitute(self.init.cube(), initmap))
        self.cnt = 0

    def get_map(self, idx):
        curr_map = [(self.vars[i], self.vardef(str(self.vars[i]) + "_" + str(idx))) for i in range(len(self.vars))]
        next_map = [
            (self.primed_vars[i], self.vardef(str(self.vars[i]) + "_" + str(idx + 1))) for i in range(len(self.vars))
        ]
        return curr_map + next_map

    def unroll(self):
        self.slv.add(substitute(simplify(self.trans.cube()), self.get_map(self.cnt)))
        self.cnt += 1

    def add(self, constraint):
        idx = self.cnt
        var_map = self.get_map(idx)
        self.slv.add(substitute(constraint, var_map))

    def check(self):
        return self.slv.check()

    def run(self, k_ind=True, k=10):
        # BASE CASE
        bmc_base = copy.deepcopy(self)
        step = 0
        if k_ind:
            bmc_kind = copy.deepcopy(bmc_base)
            bmc_kind.setup(induction=True)  # to verify P & T -> P'
            bmc_kind.add(substitute(bmc_kind.post.cube(), bmc_kind.get_map(0)))  # add p
            k = 1000
        bmc_base.setup()  # verify init & T -> P is valid
        bmc_base.slv.push()
        bmc_base.add(substitute(Not(bmc_base.post.cube()), bmc_base.get_map(0)))
        if bmc_base.check() == sat:
            print(f"Safty property Falsified: bad state is reachable from initial state!")
            # TODO: Add your trace_print function call here if needed
            return False, []
        bmc_base.slv.pop()
        
        # INDUCTION STEP
        for step in range(1, k + 1):
            if k_ind:
                print(f"Checking for CEX after {step} transitions")
                # unroll -> push -> check -> pop
                bmc_kind.unroll()
                bmc_kind.slv.push()
                # check if p&T&T&...->p' is valid
                bmc_kind.add(substitute(Not(bmc_kind.post.cube()), bmc_kind.get_map(bmc_kind.cnt)))
                if bmc_kind.check() == unsat:
                    # reached property invariant
                    print(f"Safty property Proven: get inductive invariant")
                    return True, []
                bmc_kind.slv.pop()
                
            bmc_base.unroll()
            bmc_base.slv.push()
            bmc_base.add(substitute(Not(bmc_base.post.cube()), bmc_base.get_map(bmc_base.cnt)))
            if bmc_base.check() == sat:
                print(f"Safty property Falsified: Found CEX after {step} steps")
                return False, []
            bmc_base.slv.pop()
        print(f"Invariant couldn't be proven inductive after {k} transitions")
