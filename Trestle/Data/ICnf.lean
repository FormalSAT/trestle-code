/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki, Cayden Codel
-/

import Trestle.Data.ILit

/-

Implementation of DIMACS clauses and CNF formulas.

-/

namespace Trestle

abbrev IClause := Array ILit
abbrev ICnf := Array IClause

namespace IClause

/--
  Finds the maximum DIMACS variable in a clause.
  If the clause is empty, then 0 is returned.
-/
def maxVar (C : IClause) : Nat :=
  C.map ILit.toNat |> Array.foldl max 0

end IClause

namespace ICnf
/--
  Finds the maximum DIMACS variable in the CNF.
  If there are no variables in the formula, then 0 is returned.
-/
def maxVar (F : ICnf) : Nat :=
  F.map IClause.maxVar |> Array.foldl max 0

end ICnf

end Trestle
