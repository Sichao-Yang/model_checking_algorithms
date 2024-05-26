# Model Checking Algorithms

This is my take on bmc, k-induction, ic3 algorithms. I try to provide a python version of the algorithm for each.

## Structure

This project folder is divided into code and dataset, in code you can find python and cpp implementations. Some of them are cloned and modified from other repos, a readme is given under each folder.

## Dependencies

* [aigertool](https://github.com/arminbiere/aiger): The (old) standard format and its supporting library to represent MC problem in hardware circuits. Used to convert `aig` format to `aag` format. Put it in the same directory as `main.py` by execute `git clone https://github.com/arminbiere/aiger.git` here, and build it with `./configure.sh && make`. Without this tool will only support `aag` format.

* [minisat](https://github.com/agurfinkel/minisat): The sat solver used in IC3-ref, the [original version](https://github.com/niklasso/minisat) can't be compiled with new c++11 standard (see [this thread](https://github.com/niklasso/minisat/issues/16)) and above, so please clone prof. agur finkel's version.

## Repos That inspiring

- [pybmc](https://github.com/Gy-Hu/pybmc)
- [IC3playground](https://github.com/Gy-Hu/IC3-Playground)