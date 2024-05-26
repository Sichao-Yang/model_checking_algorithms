file = 'dataset/toy1.aag'

import aiger
x, y, z = aiger.atom('x'), aiger.atom('y'), aiger.atom('z')
expr_str = '~(x | y) & z'
expr_str = 'x|y'
expr_str = '(x|y) & (~x|~y) & (~x | y ) & ~y'
expr = eval(expr_str)
print(expr.aig)
# exit()
with open(file, 'w') as fp:
    fp.write(str(expr.aig))
    fp.write('c\n{}'.format(expr_str))

import model
m = model.Model()

print(m.parse(file))


aig1 = aiger.load(file)
print(aig1)

# from pysat.formula import CNF
# cnf = CNF(from_aiger=aig1)
# print(cnf.nv)
# print(cnf.clauses)
# print(['{0} <-> {1}'.format(v, cnf.vpool.obj(v)) for v in cnf.inps])
# print(['{0} <-> {1}'.format(v, cnf.vpool.obj(v)) for v in cnf.outs])