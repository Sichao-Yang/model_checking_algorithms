from pdr import PDR
from bmc import BMC
from z3 import *
import inspect
from model import tCube
import re




def generate_variables(N):
    return [Bool(f"v{i}") for i in range(N)]


def generate_prime(variables):
    return [Bool(var.__str__() + "_prime") for var in variables]


def print_and_write(file, string):
    file.write(string + "\n")
    print(string)


def get_new_lits(tmp: tCube):
    a = str(tmp.cube())
    res = re.findall(pattern="k!\\d+", string=a)
    if len(res) == 0:
        return [], []
    else:
        res = list(set(res))
        vars = [Bool(x) for x in res]
        return vars, generate_prime(vars)


def convert_to_tcube(formula):
    tmp = tCube()
    g = Goal()
    g.add(formula)
    t = Tactic("aig")  # 转化得到该公式的 aig
    tmp.addAnds(t(g)[0])
    v, vp = get_new_lits(tmp)
    return tmp,v,vp 


def verify_program(
    expected, title, variables, primes, init, trans, post, slv_name="bmc", show_result=False, show_trans=True
):
    fname = inspect.stack()[1][3]

    with open("tmp.out", "w") as f:
        print_and_write(f, title)
        print_and_write(f, "---------------------------------------")
        print_and_write(f, "Init: " + str(init))
        f.write("Trans: " + str(trans) + "\n")
        if show_trans:
            print("Trans:", trans)
        print_and_write(f, "Post:" + str(post))
        
        trans, new_lits, new_lits_p = convert_to_tcube(trans)
        variables += new_lits
        primes += new_lits_p
        init, new_lits, new_lits_p = convert_to_tcube(init)
        variables += new_lits
        primes += new_lits_p
        
        post, new_lits, new_lits_p = convert_to_tcube(post)
        variables += new_lits
        primes += new_lits_p

        if slv_name == "pdr":
            slv = PDR([], [], variables, primes, init, trans, post, "")
        elif slv_name == "bmc":
            slv = BMC([], [], variables, primes, init, trans, post, "")
        proven, output = slv.run()
        if proven == expected:
            print_and_write(f, f"Test passed on {fname}")
        else:
            raise ValueError(f"Test failed on {fname}")
        res_string = "SAT\n" if proven else "UNSAT\n"
        print(res_string + str(output) if show_result else res_string)


def three_at_a_time():
    """
    :return: variables -> Boolean Variables, primes -> The Post Condition Variable, init -> The initial State,
    trans -> Transition Function, post -> The Safety Property
    """
    size = 8
    variables = generate_variables(size)
    primes = generate_prime(variables)

    def triple(i):
        return And(
            *[primes[j] == variables[j] for j in range(size) if (j != i and j != i - 1 and j != i - 2)]
            + [
                Not(primes[i] == variables[i]),
                Not(primes[i - 1] == variables[i - 1]),
                Not(primes[i - 2] == variables[i - 2]),
            ]
        )

    init = And(*[variables[i] for i in range(size - 1)] + [(variables[-1])])
    print("init:", init)
    trans = Or(*[triple(i) for i in range(size)])
    print("trans:", trans)
    post = Or(*variables)
    print("post:", post)

    verify_program(
        True,
        """SAFE
Similar to OneAtATime
A boolean bit vector is initialized with size 8
to TTTTTTTT. One bit can be flipped per frame but
now the two neighbors to it's left must also flip for a total of three.
The post condition is that at least one bool is True
which cannot be violated with a bit vector of size 8 and three bits flipped per frame""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def three_at_a_time_odd():
    size = 9
    variables = generate_variables(size)
    primes = generate_prime(variables)

    def triple(i):
        return And(
            *[primes[j] == variables[j] for j in range(size) if (j != i and j != i - 1 and j != i - 2)]
            + [
                Not(primes[i] == variables[i]),
                Not(primes[i - 1] == variables[i - 1]),
                Not(primes[i - 2] == variables[i - 2]),
            ]
        )

    init = And(*[variables[i] for i in range(size - 1)] + [(variables[-1])])
    trans = Or(*[triple(i) for i in range(size)])
    post = Or(*variables)

    verify_program(
        False,
        """UNSAFE
Three at a time but with an odd length bit vector
The post condition can now be violated flipping three bits at a time""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def boolean_shifter():
    len = 10
    variables = [Bool(str(i)) for i in range(len)]
    primes = [Bool(str(i) + "'") for i in variables]

    # initialize to something like [T T T T T T T T F]
    init = And(*[variables[i] for i in range(len - 1)] + [Not(variables[-1])])
    trans = And(*[primes[i] == And(variables[i - 1], variables[i - 2]) for i in range(len)])
    post = Or(*variables)

    verify_program(
        False,
        """UNSAFE
Initialize a boolean bitfield to [TTTTTTTTTF]
Each iteration, each boolean takes the AND of the two bits to its left
(rolling over at the left back to the right)
(Frame 1 will look like [FFTTTTTTTT])
The post condition is simply that at least one boolean be true,
which can take quite a while to fail depending on the width of the bitfield""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def boolean_incrementer():
    len = 8
    variables = [Bool(str(i)) for i in range(len)]
    primes = [Bool(str(i) + "'") for i in variables]
    init = And(*[Not(variables[i]) for i in range(len - 1)] + [variables[-1]])
    print("init is:", init)

    def carryout(pos):
        if pos == len / 2:
            return False
        else:
            return Or(
                And(Xor(variables[pos], variables[pos + len / 2]), carryout(pos + 1)),
                And(variables[pos], variables[pos + len / 2]),
            )

    trans = And(
        *[primes[i] == Xor(Xor(variables[i], variables[i + len / 2]), carryout(i + 1)) for i in range(len / 2)]
        + [primes[i + len / 2] == variables[i + len / 2] for i in range(len / 2)]
    )
    print("trans is:", trans)
    post = Not(And(*[variables[i] for i in range(len / 2)]))
    print("post is:", post)
    verify_program(
        False,
        """UNSAFE
Initialize a boolean bitfield [AAAAA BBBBB]
Each iteration, add the value of BBBBB to AAAAA
incrementing it
In this example, BBBBB is 00001 and the postcondition is that
AAAAA is not 11111, which is unsafe after 16 frames""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def incrementer_overflow():
    size = 8
    overflow = Bool("Overflow")
    variables = [Bool(str(i)) for i in range(size)] + [overflow]
    primes = [Bool(str(i) + "'") for i in variables]
    overflowprime = primes[-1]
    init = And(*[Not(variables[i]) for i in range(size - 1)] + [variables[size - 1], overflow == False])

    def carryout(pos):
        if pos == size / 2:
            return False
        else:
            return Or(
                And(Xor(variables[pos], variables[pos + size / 2]), carryout(pos + 1)),
                And(variables[pos], variables[pos + size / 2]),
            )

    trans = If(
        And(*[variables[i] for i in range(size / 2)]),
        And(*[variables[i] == primes[i] for i in range(len(variables))]),
        And(
            *[primes[i] == Xor(Xor(variables[i], variables[i + size / 2]), carryout(i + 1)) for i in range(size / 2)]
            + [primes[i + size / 2] == variables[i + size / 2] for i in range(size / 2)]
            + [overflowprime == carryout(0)]
        ),
    )
    post = Not(overflow)
    verify_program(
        True,
        """SAFE
Add overflow protection to the previous boolean incrementer
When the incrementer becomes full, it will not add any more to it
There is an overflow bit that gets set if there is any carryover from the MSB
so the postcondition is Not(overflow)""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def even_incrementer():
    len = 6
    variables = [Bool(str(i)) for i in range(len)]
    primes = [Bool(str(i) + "'") for i in variables]
    init = And(*[Not(variables[i]) for i in range(len - 2)] + [variables[-2], Not(variables[-1])])

    def carryout(pos):
        if pos == len / 2:
            return False
        else:
            return Or(
                And(Xor(variables[pos], variables[pos + len / 2]), carryout(pos + 1)),
                And(variables[pos], variables[pos + len / 2]),
            )

    trans = And(
        *[primes[i] == Xor(Xor(variables[i], variables[i + len / 2]), carryout(i + 1)) for i in range(len / 2)]
        + [primes[i + len / 2] == variables[i + len / 2] for i in range(len / 2)]
    )
    post = Not(variables[len / 2 - 1])
    verify_program(
        True,
        """SAFE
Using the same boolean incrementer from before
In this example, BBB is 010 and the postcondition is that
AAA is even, which is safe""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def swapper():
    x = Bool("x")
    y = Bool("y")
    z = Bool("z")
    xp = Bool("x'")
    yp = Bool("y'")
    zp = Bool("z'")
    variables = [x, y, z]
    primes = [xp, yp, zp]

    init = And(x, Not(y), Not(z))
    trans = And(xp == y, zp == x, yp == z)
    post = Or(x, y, z)
    verify_program(
        True,
        """SAFE
This test is a simple program that rotates the variables of three booleans
The post condition is that at least one of them must be true
which is inductive because one is initialized to true and never negated, only swapped""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def one_at_a_time():
    size = 8
    variables = generate_variables(size)
    primes = generate_prime(variables)

    def exclusive(i):  # only one variable will be different
        return And(*[primes[j] == variables[j] for j in range(size) if j != i] + [Not(primes[i] == variables[i])])

    init = And(*[variables[i] for i in range(size - 1)] + [(variables[-1])])
    # init = And(*[variables[i] for i in range(size)])
    print("init:", init)
    trans = Or(*[exclusive(i) for i in range(size)])
    print("trans:", trans)  # this measns one of the state variable will be different after transition
    post = Or(*variables)
    print("post:", post)

    verify_program(
        False,
        """UNSAFE
A boolean bit vector is initialized with size 8
to TTTTTTTT. One bit can be flipped per frame. 
The post condition is that at least one bool is True
which can be violated in 8 frames""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def counter_unsat():
    variables = [BitVec("x", 8)]
    x = variables[0]
    primes = [BitVec("x'", 8)]
    xp = primes[0]
    verify_program(
        False,
        """Counter (unsatisfiable)
    Adds one to x as long as x < 64. Asserts that x remains less than 10.""",
        variables,
        primes,
        And(x == 0),
        Or(And(xp == x + 1, x < 64), xp == x),
        x < 10,
    )


def counter_sat():
    variables = [BitVec("x", 5)]
    x = variables[0]
    primes = [BitVec("x'", 5)]
    xp = primes[0]
    verify_program(
        True,
        """Counter (satisfiable)
    Adds one to x as long as x < 7. Asserts that x remains less than 6.
    x is a 5 bit signed number, so it must only rule out 7 <= x <= 15.""",
        variables,
        primes,
        And(x == 0),
        Or(And(xp == x + 1, x < 6), xp == x),
        x < 7,
    )


def add_sub_unsat():
    variables = [BitVec("x", 6), BitVec("y", 6)]
    x, y = variables
    primes = [BitVec("x'", 6), BitVec("y'", 6)]
    xp, yp = primes
    init = And(x == 4, y == 3)
    trans = And(xp == x + y, yp == x - y)
    post = Not(x == 32)
    verify_program(
        False,
        """Addition and subtraction (unsatisfiable)
    x <- x + y, y <- x - y
    The values of x and y jump around and in frame 6, x = 32""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def add_sub_sat():
    variables = [BitVec("x", 3), BitVec("y", 3)]
    x, y = variables
    primes = [BitVec("x'", 3), BitVec("y'", 3)]
    xp, yp = primes
    init = And(x == 4, y == 3)
    trans = And(xp == x + y, yp == x - y)
    post = Not(x == 2)
    verify_program(
        True,
        """Addition and subtraction (satisfiable)
    x <- x + y, y <- x - y
    The values of x and y jump around, but x can never hold the value 2""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def shifter_unsat():
    variables = generate_variables(4)
    primes = generate_prime(variables)
    init = And(*[var == False for var in variables[1:]])
    trans = And(*[primes[i] == variables[i - 1] for i in range(len(variables))])
    post = variables[-1] == False
    verify_program(
        False,
        """Shifter (unsatisfiable)
        Starting with all but the LSB False, can the MSB remain False?""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def shifter_sat():
    variables = generate_variables(4)
    primes = generate_prime(variables)
    init = variables[0]
    trans = And(*[primes[i] == variables[i - 1] for i in range(len(variables))])
    post = Or(*[var for var in variables])
    verify_program(
        True,
        """Shifter (satisfiable)
    Starting with the LSB set to True, maintain at least one bit True""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def lights_out_sat():
    LEN = 9
    variables = generate_variables(LEN)
    primes = generate_prime(variables)
    on_bits = [0, 1, 2, 5, 6, 7, 8]
    init = And(
        *([variables[i] for i in on_bits] + [Not(variable) for i, variable in enumerate(variables) if not i in on_bits])
    )
    trans = Or(
        [
            And(
                *[
                    (
                        (primes + primes)[j] == Not((variables + variables)[j])
                        if abs(j - i) <= 1 or abs(j - i) == LEN - 1
                        else (primes + primes)[j] == (variables + variables)[j]
                    )
                    for j in range(LEN)
                ]
            )
            for i in range(LEN)
        ]
    )
    post = Or(*[var for var in variables])
    verify_program(
        True,
        """Lights out (satisfiable)
    Each step in the program represents a move of inverting a bit and its neighboring bits.
    For it to be unsolvable, neighboring bits must include wrapping around.
    Returning SAT means there is no solution to the starting conditions resulting in turning off all the bits.""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def lights_out_unsat():
    LEN = 9
    variables = generate_variables(LEN)
    primes = generate_prime(variables)
    on_bits = [0, 1, 2, 5, 6, 7, 8]
    init = And(
        *([variables[i] for i in on_bits] + [Not(variable) for i, variable in enumerate(variables) if not i in on_bits])
    )
    trans = Or(
        [
            And(
                *[
                    (
                        (primes + primes)[j] == Not((variables + variables)[j])
                        if abs(j - i) <= 1
                        else (primes + primes)[j] == (variables + variables)[j]
                    )
                    for j in range(LEN)
                ]
            )
            for i in range(LEN)
        ]
    )
    post = Or(*[var for var in variables])
    verify_program(
        False,
        """Lights out (unsatisfiable)
    Each step in the program represents a move of inverting a bit and its neighboring bits.
    In this version neighboring bits do not wrap around.
    Returning UNSAT means there is a solution to the starting conditions resulting in turning off all the bits.""",
        variables,
        primes,
        init,
        trans,
        post,
    )


def run_all():
    [test() for test in tests[1:]]


tests = [
    run_all,
    ### bitvec ones
    # counter_sat,
    # counter_unsat,
    # add_sub_sat,
    # add_sub_unsat,
    shifter_sat,
    shifter_unsat,
    lights_out_sat,
    lights_out_unsat,
    swapper,
    one_at_a_time,
    three_at_a_time,
    three_at_a_time_odd,
    ### large_ones:
    # boolean_shifter,
    # boolean_incrementer,
    # incrementer_overflow,
    # even_incrementer,
]


def main():
    import time

    s = time.time()

    test_lookup = {test.__name__: test for test in tests}
    if len(sys.argv) < 2:
        value = "shifter_unsat"
        print("Usage: python test_pdy.py [{}]".format(", ".join([test.__name__ for test in tests])))
        print("set to default value: {value}")
        sys.argv.append(value)
    #     exit()

    test_lookup[sys.argv[1]]()

    print("test time: {}".format(time.time() - s))


if __name__ == "__main__":

    from pyinstrument import Profiler

    with Profiler(interval=0.1) as profiler:
        main()
    profiler.print()
