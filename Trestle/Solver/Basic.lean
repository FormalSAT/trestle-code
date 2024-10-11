/-
Copyright (c) 2024 The LeanSAT Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio
-/

import Trestle.Data.ICnf
/-import Batteries.Data.HashMap
import LeanSAT.Data.Cnf
import LeanSAT.Data.HashAssn
import LeanSAT.Data.ICnf

open Batteries -/

namespace Trestle.Solver

abbrev Assn := Array ILit

/--
  The result of a call to a SAT solver.
-/
inductive SolverResult
  | sat (assn : Assn)
  | unsat
  | error
deriving DecidableEq, Repr, Inhabited

namespace SolverResult

instance instToString : ToString SolverResult where
  toString  | .error => "error"
            | .unsat => "unsat"
            | .sat assn => s!"sat: {assn}"

def isSat : SolverResult → Bool
  | .sat _  => true
  | _       => false

def getAssn? : SolverResult → Option Assn
| .sat assn => some assn
| _         => none

end SolverResult

end Solver   -- end the namespace briefly so we can define the `Solver` class

class Solver (m : Type → Type v) where
  solve : [Monad m] → ICnf → m Solver.SolverResult

class ModelCount (m : Type → Type v) [outParam (Monad m)] where
  modelCount : ICnf → Option (List IVar) → m Nat

class ModelSample (m : Type → Type v) where
  modelSample : ICnf → Option (List IVar) → Nat → m (List Solver.Assn)
