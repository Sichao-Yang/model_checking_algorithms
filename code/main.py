import subprocess
import argparse
import os, os.path, shutil
import sys
from pathlib import Path
import time
import argparse
import z3
import tempfile
import copy
from utils.formula import from_z3
from os import path as osp
import model
import bmc
import pdr


def convert_aig_to_aag(file, m):
    aig_path = file
    with tempfile.TemporaryDirectory() as tmpdirname:
        aigtoaig_cmd = "./aiger/aigtoaig"
        tmpdir = Path(tmpdirname)
        filepath = osp.join(tmpdir, "tmp.aag")
        shutil.copy(aig_path, tmpdir)
        subprocess.call([aigtoaig_cmd, aig_path, filepath])
        return m.parse(filepath)


def convert_z3_to_dimacs(z3_expr):  # z3_expr is a z3 expression, e.g. bmc.slv.assertions()
    f = from_z3(z3_expr)
    # cnf_string_lst = f.to_dimacs_string()
    # print(cnf_string_lst)
    f.to_dimacs_file("tmp.cnf")


if __name__ == "__main__":
    import time

    s = time.time()

    file = "dataset/aig_benchmark/hwmcc07/tip/nusmv.syncarb5^2.B.aig"   # UNSAT
    # file = "dataset/aig_benchmark/hwmcc07/tip/cmu.periodic.N.aig"  # UNSAT
    # file = 'dataset/aig_benchmark/hwmcc07/l2s/139442p0neg.aig'  # SAT
    
    help_info = "Usage: python main.py <file-name>.aag (or <file-name>.aig) --k <unrolling steps>"
    parser = argparse.ArgumentParser(description="Run tests examples on the BMC algorithm")
    parser.add_argument("--aag", type=str, help="The name of the test to run", default=file, nargs="?")
    parser.add_argument("--k", type=int, help="The number of unrolling steps", default=10, nargs="?")
    parser.add_argument(
        "--mode", type=str, help="The mode of the algorithm, input bmc or k-ind", default="k-ind", nargs="?"
    )
    args = parser.parse_args()

    m = model.Model()
    file = args.aag
    if file.endswith(".aig"):
        inputs = convert_aig_to_aag(file, m)
    else:
        inputs = m.parse(file)

    if args.mode in ["bmc", "k-ind"]:
        slv = bmc.BMC(*inputs)
        if args.mode == "bmc":
            print("Now running bmc")
            slv.run(k_ind=False, k=args.k)
        elif args.mode == "k-ind":
            print("Now running k-induction")
            slv.run()
    elif args.mode == "pdr":
        slv = pdr.PDR(*inputs)
        slv.run()

    print("time spend: {}".format(time.time() - s))
