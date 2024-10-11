/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

-- Mostly used for backwards-induction proofs
theorem Nat.eq_sub_add_of_add_eq_sub {k l m n : Nat} : k + l = n - m → k = n - (m + l) := by
  omega
