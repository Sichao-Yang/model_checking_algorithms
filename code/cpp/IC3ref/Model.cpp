/*********************************************************************
Copyright (c) 2013, Aaron Bradley

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include <iostream>

#include "Model.h"
#include "SimpSolver.h"
#include "Vec.h"

Minisat::Var Var::gvi = 0;

Model::~Model()
{
  if (inits)
    delete inits;
  if (sslv)
    delete sslv;
}

const Var &Model::primeVar(const Var &v, Minisat::SimpSolver *slv)
{
  // var for false
  if (v.index() == 0)
    return v;
  // latch or PI
  if (v.index() < reps)
    return vars[primes + v.index() - inputs];
  // AND lit
  assert(v.index() >= reps && v.index() < primes);
  // created previously?
  IndexMap::const_iterator i = primedAnds.find(v.index());
  size_t index;
  if (i == primedAnds.end())
  {
    // no, so make sure the model hasn't been locked
    assert(primesUnlocked);
    // create a primed version
    stringstream ss;
    ss << v.name() << "'";
    index = vars.size();
    vars.push_back(Var(ss.str()));
    if (slv)
    {
      Minisat::Var _v = slv->newVar();
      assert(_v == vars.back().var());
    }
    assert(vars.back().index() == index);
    primedAnds.insert(IndexMap::value_type(v.index(), index));
  }
  else
    index = i->second;
  return vars[index];
}

Minisat::Solver *Model::newSolver() const
{
  Minisat::Solver *slv = new Minisat::Solver();
  // load all variables to maintain alignment
  for (size_t i = 0; i < vars.size(); ++i)
  {
    Minisat::Var nv = slv->newVar();
    assert(nv == vars[i].var());
  }
  return slv;
}

void Model::loadTransitionRelation(Minisat::Solver &slv, bool primeConstraints)
{ // T(s, s')
  if (!sslv)
  {
    // create a simplified CNF version of (this slice of) the TR
    sslv = new Minisat::SimpSolver();
    // introduce all variables to maintain alignment
    for (size_t i = 0; i < vars.size(); ++i)
    {
      Minisat::Var nv = sslv->newVar();
      assert(nv == vars[i].var());
    }
    // freeze inputs, latches, and special nodes (and primed forms)
    // The code marks the variable as "frozen" in the SAT solver, 
    // meaning these variables should not be eliminated during preprocessing. 
    // This is done for both the variable and its primed counterpart.
    for (VarVec::const_iterator i = beginInputs(); i != endInputs(); ++i)
    {
      sslv->setFrozen(i->var(), true);
      sslv->setFrozen(primeVar(*i).var(), true);
    }
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
    {
      sslv->setFrozen(i->var(), true);
      sslv->setFrozen(primeVar(*i).var(), true);
    }
    sslv->setFrozen(varOfLit(error()).var(), true);
    sslv->setFrozen(varOfLit(primedError()).var(), true);
    for (LitVec::const_iterator i = constraints.begin();
         i != constraints.end(); ++i)
    {
      Var v = varOfLit(*i);
      sslv->setFrozen(v.var(), true);
      sslv->setFrozen(primeVar(v).var(), true);
    }
    // initialize with roots of required formulas
    // require is a set of literals that need to be included in the CNF, 
    // including the next state functions for all latches and the error condition.
    // prequire is a similar set but for primed formulas.
    // if nextstate is n0 <=> x1 & x2, then this will be included
    LitSet require; // unprimed formulas
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
      require.insert(nextStateFn(*i));
    require.insert(_error);
    require.insert(constraints.begin(), constraints.end());
    LitSet prequire; // for primed formulas; always subset of require
    prequire.insert(_error);
    prequire.insert(constraints.begin(), constraints.end());
    // Traverse AIG Backward:
    // The code iterates through the AIG (And-Inverter Graph) in reverse to encode each gate into CNF format.
    // If a gate's output is not required, it is skipped.
    // For each gate, the CNF clauses representing the AND gate are added to the SAT solver.
    // The inputs to the gate are also marked as required.
    // If the primed form of the gate's output is required, the corresponding CNF clauses for the primed form are added.
    for (AigVec::const_reverse_iterator i = aig.rbegin();
         i != aig.rend(); ++i)
    {
      // skip if this row is not required
      if (require.find(i->lhs) == require.end() && require.find(~i->lhs) == require.end())
        continue;
      // encode into CNF
      sslv->addClause(~i->lhs, i->rhs0);
      sslv->addClause(~i->lhs, i->rhs1);
      sslv->addClause(~i->rhs0, ~i->rhs1, i->lhs);
      // require arguments
      require.insert(i->rhs0);
      require.insert(i->rhs1);
      // primed: skip if not required
      if (prequire.find(i->lhs) == prequire.end() && prequire.find(~i->lhs) == prequire.end())
        continue;
      // encode PRIMED form into CNF
      Minisat::Lit r0 = primeLit(i->lhs, sslv),
                   r1 = primeLit(i->rhs0, sslv),
                   r2 = primeLit(i->rhs1, sslv);
      sslv->addClause(~r0, r1);
      sslv->addClause(~r0, r2);
      sslv->addClause(~r1, ~r2, r0);
      // require arguments
      prequire.insert(i->rhs0);
      prequire.insert(i->rhs1);
    }
    // assert literal for true
    sslv->addClause(btrue());
    // assert ~error, constraints, and primed constraints
    sslv->addClause(~_error);
    for (LitVec::const_iterator i = constraints.begin();
         i != constraints.end(); ++i)
    {
      sslv->addClause(*i);
    }
    // Assert Latch Equivalence:
    // For each latch, asserts that the next state function equals the 
    // primed version of the latch.
    // assert l' = f for each latch l
    for (VarVec::const_iterator i = beginLatches(); i != endLatches(); ++i)
    {
      Minisat::Lit platch = primeLit(i->lit(false)), f = nextStateFn(*i);
      sslv->addClause(~platch, f);    // (~a or b) and (a or ~b): a<->b
      sslv->addClause(~f, platch);
    }
    sslv->eliminate(true); // Eliminate Unnecessary Variables
  }

  // load the clauses from the simplified context
  while (slv.nVars() < sslv->nVars())
    slv.newVar();
  for (Minisat::ClauseIterator c = sslv->clausesBegin();
       c != sslv->clausesEnd(); ++c)
  {
    const Minisat::Clause &cls = *c;
    Minisat::vec<Minisat::Lit> cls_;
    for (int i = 0; i < cls.size(); ++i)
      cls_.push(cls[i]);
    slv.addClause_(cls_);
  }
  for (Minisat::TrailIterator c = sslv->trailBegin();
       c != sslv->trailEnd(); ++c)
    slv.addClause(*c);
  if (primeConstraints)
    for (LitVec::const_iterator i = constraints.begin();
         i != constraints.end(); ++i)
      slv.addClause(primeLit(*i));
}

void Model::loadInitialCondition(Minisat::Solver &slv) const
{
  slv.addClause(btrue());
  for (LitVec::const_iterator i = init.begin(); i != init.end(); ++i)
    slv.addClause(*i);
  if (constraints.empty())
    return;
  // impose invariant constraints on initial states (AIGER 1.9)
  LitSet require;
  require.insert(constraints.begin(), constraints.end());
  for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend(); ++i)
  {
    // skip if this (*i) is not required
    if (require.find(i->lhs) == require.end() && require.find(~i->lhs) == require.end())
      continue;
    // encode into CNF
    slv.addClause(~i->lhs, i->rhs0);
    slv.addClause(~i->lhs, i->rhs1);
    slv.addClause(~i->rhs0, ~i->rhs1, i->lhs);
    // require arguments
    require.insert(i->rhs0);
    require.insert(i->rhs1);
  }
  for (LitVec::const_iterator i = constraints.begin();
       i != constraints.end(); ++i)
    slv.addClause(*i);
}

void Model::loadError(Minisat::Solver &slv) const
{
  LitSet require; // unprimed formulas
  require.insert(_error);
  // traverse AIG backward
  for (AigVec::const_reverse_iterator i = aig.rbegin(); i != aig.rend(); ++i)
  {
    // skip if this row is not required
    if (require.find(i->lhs) == require.end() && require.find(~i->lhs) == require.end())
      continue;
    // encode into CNF a <=> (b&c), !a|b, !a|c, !b|!c|a, https://en.wikipedia.org/wiki/Tseytin_transformation
    slv.addClause(~i->lhs, i->rhs0);
    slv.addClause(~i->lhs, i->rhs1);
    slv.addClause(~i->rhs0, ~i->rhs1, i->lhs);
    // require arguments
    require.insert(i->rhs0);
    require.insert(i->rhs1);
  }
}

bool Model::isInitial(const LitVec &latches)
{
  if (constraints.empty())
  {
    // an intersection check (AIGER 1.9 w/o invariant constraints)
    if (initLits.empty())
      initLits.insert(init.begin(), init.end());
    for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i)
      if (initLits.find(~*i) != initLits.end())
        return false;
    return true;
  }
  else
  {
    // a full SAT query
    if (!inits)
    {
      inits = newSolver();
      loadInitialCondition(*inits);
    }
    Minisat::vec<Minisat::Lit> assumps;
    assumps.capacity(latches.size());
    for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i)
      assumps.push(*i);
    return inits->solve(assumps);
  }
}

// Creates a named variable.
Var var(const aiger_symbol *syms, size_t i, const char prefix,
        bool prime = false)
{
  const aiger_symbol &sym = syms[i];
  stringstream ss;
  if (sym.name)
    ss << sym.name;
  else
    ss << prefix << i;
  if (prime)
    ss << "'";
  return Var(ss.str());
}

Minisat::Lit lit(const VarVec &vars, unsigned int l)
{
  return vars[l >> 1].lit(aiger_sign(l));
}

Model *modelFromAiger(aiger *aig, unsigned int propertyIndex)
{
  VarVec vars(1, Var("false"));           // variable list
  LitVec init, constraints, nextStateFns; // literal (variable with sign) relations

  // declare primary inputs and latches
  for (size_t i = 0; i < aig->num_inputs; ++i)
    vars.push_back(var(aig->inputs, i, 'i'));
  for (size_t i = 0; i < aig->num_latches; ++i)
    vars.push_back(var(aig->latches, i, 'l'));

  // the AND section
  AigVec aigv;
  for (size_t i = 0; i < aig->num_ands; ++i)
  {
    // 1. create a representative
    stringstream ss;
    ss << 'r' << i;
    vars.push_back(Var(ss.str())); // r0, r1, r2
    const Var &rep = vars.back();
    // 2. obtain arguments of AND as lits
    Minisat::Lit l0 = lit(vars, aig->ands[i].rhs0);
    Minisat::Lit l1 = lit(vars, aig->ands[i].rhs1);
    // 3. add AIG row
    aigv.push_back(AigRow(rep.lit(false), l0, l1));
  }

  // acquire latches' initial states and next-state functions
  for (size_t i = 0; i < aig->num_latches; ++i)
  {
    const Var &latch = vars[1 + aig->num_inputs + i];
    // initial condition
    unsigned int r = aig->latches[i].reset;
    if (r < 2)
      init.push_back(latch.lit(r == 0));
    // next-state function, because its current state variable can be
    // recovered from vars and index offset, so no need to record it as a
    // vector of tuples (current lit, next lit)
    nextStateFns.push_back(lit(vars, aig->latches[i].next));
  }

  // invariant constraints
  for (size_t i = 0; i < aig->num_constraints; ++i)
    constraints.push_back(lit(vars, aig->constraints[i].lit));

  // acquire error from given propertyIndex
  if ((aig->num_bad > 0 && aig->num_bad <= propertyIndex) || (aig->num_outputs > 0 && aig->num_outputs <= propertyIndex))
  {
    cout << "Bad property index specified." << endl;
    return 0;
  }
  Minisat::Lit err =
      aig->num_bad > 0
          ? lit(vars, aig->bad[propertyIndex].lit)
          : lit(vars, aig->outputs[propertyIndex].lit);

  size_t offset = 0;
  return new Model(vars,
                   offset += 1, offset += aig->num_inputs,
                   offset + aig->num_latches,
                   init, constraints, nextStateFns, err, aigv);
}
