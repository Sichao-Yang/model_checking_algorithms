import argparse
import sys
import time
from pyinstrument import Profiler
from os import path as osp

root = osp.abspath(osp.join(__file__, "../../../"))
# print(f"project root: {root}")
sys.path.append(root)
from test_cases import *


def run_all(args):
    [test(args) for test in tests[1:]]


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
    ### take aig as input
    comp_circuits,
]


def main():

    s = time.time()

    filepath = "dataset/aig_benchmark/hwmcc07/tip/nusmv.syncarb5^2.B.aig"  # UNSAT
    # filepath = "dataset/aig_benchmark/hwmcc07/tip/cmu.periodic.N.aig"  # UNSAT
    # filepath = 'dataset/aig_benchmark/hwmcc07/l2s/139442p0neg.aig'  # SAT
    filepath = osp.join(root, filepath)
    print(filepath)
    parser = argparse.ArgumentParser(description="Run tests examples on the BMC algorithm")
    parser.add_argument(
        "-aag", type=str, help="The name of the aag file to run in comp_circuits test", default=filepath, nargs="?"
    )
    parser.add_argument("-k", type=int, help="The number of unrolling steps", default=10, nargs="?")
    parser.add_argument(
        "-mode", type=str, help="The mode of the algorithm, input bmc or k-ind", default="pdr", nargs="?"
    )
    parser.add_argument("-testname", type=str, help="test name", default="comp_circuits", nargs="?")
    args = parser.parse_args()

    test_lookup = {test.__name__: test for test in tests}

    test_lookup[args.testname](args)

    print("test time: {}".format(time.time() - s))


if __name__ == "__main__":

    with Profiler(interval=0.1) as profiler:
        main()
    profiler.print()
