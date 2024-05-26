from z3 import *
from queue import PriorityQueue
from model import tCube


def get_trace_from_PQ(pq):
    trace = list()
    while not pq.empty():
        idx, cube = pq.get()
        trace.append(cube)
    return trace


def debug_printQ(Q):
    Q_ = copy.deepcopy(Q)
    while not Q_.empty():
        print(Q_.get())


class PDR:
    def __init__(self, inputs, primed_inputs, vars, primed_vars, init, trans, post, filename):
        self.vars = vars + inputs
        self.primed_vars = primed_vars + primed_inputs
        self.init = init
        self.trans = trans
        self.post = post
        self.filename = filename
        self.frames = [self.init]
        self.lMap = {str(l): l for l in self.vars}
        self.primeMap = [(self.vars[i], self.primed_vars[i]) for i in range(len(self.vars))]

    def add_new_frame(self):
        print(f"Adding new frame {len(self.frames)}...")
        new_frame = self.post.clone()
        new_frame.t = len(self.frames)
        self.frames.append(new_frame)

    def run(self):
        cube = self.getBadCube(base=True)
        if cube:
            print(f"Safty property Falsified: bad state is reachable from initial state!")
            return False, [cube]
        print("Passed base check: I&P")
        self.add_new_frame()
        while True:
            cube = self.getBadCube(base=False)
            if cube is not None:
                # Recursive blocking stage
                trace = self.recBlockCube(cube)
                if trace is not None:
                    print(f"Safty property Falsified: Found CEX after {len(self.frames)} steps")
                    return False, trace
            else:
                self.add_new_frame()
                # Propagation stage
                for index, frame in enumerate(self.frames[:-1]):
                    invariant = self.checkForInduction(frame)
                    if invariant is not None:
                        print(f"Safty property Proven: get inductive invariant")
                        return True, invariant
                    literals = frame - self.frames[index + 1]
                    s = Solver()
                    s.add(And(frame.cube(), self.trans.cube()))
                    for c in literals:
                        s.push()
                        # if (F[i] and T and Not(c)') == unsat, it means F[i] & T => c', c can be added to F[i+1]
                        s.add(Not(substitute(c, self.primeMap)))
                        if s.check() == unsat:
                            self.frames[index + 1].addAnds([c])
                        s.pop()

    # Checks whether the we have found an inductive invariant
    def checkForInduction(self, frame):
        check_frame = frame.cube()
        s = Solver()
        s.add(And(self.trans.cube(), check_frame, Not(substitute(check_frame, self.primeMap))))
        if s.check() == unsat:
            return check_frame
        return None

    def recBlockCube(self, cube: tCube):
        # print("recBlockCube now...")
        Q = PriorityQueue()
        Q.put((cube.t, cube))
        while not Q.empty():
            i, s = Q.get()
            if i == 0:  # CEX found!
                Q.put((i, s))
                return get_trace_from_PQ(Q)
            if self.check_from_current_frame(s) is None:
                continue
            # c = self.solveRelative(s)
            c = self.check_from_last_frame(s)
            if c is not None:
                Q.put((s.t - 1, c))
                Q.put((i, s))
            else:
                for i in range(1, s.t + 1):
                    self.frames[i].addAnds([Not(s.cube())])
                # only when s is not the last frame, this proof obligation is added
                if s.t < len(self.frames) - 1:
                    s_up = copy.deepcopy(s)
                    s_up.t = s.t + 1
                    Q.put((s_up.t, s_up))
        return None

    def check_from_current_frame(self, cube):
        s = Solver()
        # Fi->!s
        s.add(And(self.frames[cube.t].cube(), cube.cube()))
        if s.check() == unsat:
            return None
        return s.model()

    def MIC(self, q: tCube):
        # Generalization
        for i in range(len(q.cubeLiterals)):
            q1 = q.delete(i)
            if self.down(q1):
                q = q1
        return q

    def down(self, q: tCube):
        while True:
            s = Solver()
            # check base case, q is candidate for generalized bad states, if I&q == sat, initial state contains q, which is not correct
            s.push()
            s.add(And(self.frames[0].cube(), q.cube()))
            if s.check() == sat:
                return False
            s.pop()
            # check consecution, F[i-1] & T => !q',
            s.push()
            s.add(
                # And(self.frames[q.t].cube(), Not(q.cube()), self.trans.cube(), substitute(q.cube(), self.primeMap))
                And(self.frames[q.t - 1].cube(), substitute(q.cube(), self.primeMap))
            )
            if unsat == s.check():
                return True
            # m = s.model()
            # q.addModel(self.lMap, m)
            # s.pop()
            return False

    # tcube is bad state
    def solveRelative(self, cube):
        s = Solver()
        s.add(self.frames[cube.t - 1].cube())
        s.add(self.trans.cube())
        s.add(Not(cube.cube()))
        s.add(substitute(cube.cube(), self.primeMap))  # F[i - 1] and T and Not(badCube) and badCube'
        if s.check() == sat:
            model = s.model()
            c = tCube(cube.t - 1)
            c.addModel(self.lMap, model)  # c = sat_model
            return c
        return None

    def check_from_last_frame(self, cube):
        s = Solver()
        # check F[i-1]&T->!s' is valid, if not, return the predecessor
        s.add(And(self.frames[cube.t - 1].cube(), self.trans.cube(), substitute(cube.cube(), self.primeMap)))
        ## F[i-1]&T&!s->!s'
        # s.add(And(self.frames[cube.t - 1].cube(), self.trans, Not(cube.cube()), substitute(cube.cube(), self.primeMap)))
        if s.check() == sat:
            model = s.model()
            c = tCube(cube.t - 1)
            c.addModel(self.lMap, model)
            return c
        return None

    def getBadCube(self, base):
        s = Solver()
        if base:
            # if I&!p is sat, bad cube found
            check_p = And(self.frames[-1].cube(), Not(self.post.cube()))
        else:
            # T&F&!p' is sat, bad cube found
            check_p = And(self.trans.cube(), self.frames[-1].cube(), Not(substitute(self.post.cube(), self.primeMap)))
        s.add(check_p)
        if s.check() == sat:
            res = tCube(len(self.frames) - 1)
            res.addModel(self.lMap, s.model())
            return res
        return None


if __name__ == "__main__":
    pass
