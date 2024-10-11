/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel, Wojciech Nawrocki, James Gallicchio
-/

import Trestle.Upstream.ToBatteries

namespace Array

/--
  A variant of `Array.set` that resizes (fills, hence the `F`) the array
  to make room for the new element. Resizing fills the array with
  the `default`.

  TODO: Write custom C code for this.
-/
@[specialize]
def setF (A : Array α) (i : Nat) (v default : α) : Array α :=
  if hi : i < A.size then
    A.set ⟨i, hi⟩ v
  else
    let rec go (j : Nat) (A' : Array α) : Array α :=
      match j with
      | 0 => A'.push v
      | j + 1 => go j (A'.push default)
    go (i - A.size) A

-- CC: A `PPA` invariant needs basic reasoning about `setF`, so we prove some lemmas.

theorem setF_lt {A : Array α} {i : Nat} (hi : i < A.size) (v default : α) :
    A.setF i v default = A.set ⟨i, hi⟩ v := by
  simp [setF, hi]

theorem setF_lt' {A : Array α} (i : Fin A.size) (v default : α) :
    A.setF i v default = A.set i v :=
  Array.setF_lt i.isLt _ _

@[simp]
theorem setF_eq (A : Array α) (v default : α) :
    A.setF A.size v default = A.push v := by
  simp [setF, setF.go]

theorem setF_go_eq (A : Array α) (i : Nat) (v default : α) :
    setF.go v default i A = (A ++ mkArray i default).push v := by
  induction i generalizing A with
  | zero => rfl
  | succ i ih =>
    rw [setF.go, ih (push A default)]
    simp only [Array.push_eq_append_singleton, mkArray_succ, Array.append_assoc]

theorem setF_gt {A : Array α} {i : Nat} (hi : i > A.size) (v default : α) :
    A.setF i v default = A ++ mkArray (i - A.size) default ++ #[v] := by
  simp [setF, Nat.lt_asymm hi, Array.setF_go_eq]; rfl

@[simp]
theorem size_setF (A : Array α) (i : Nat) (v default : α) :
    (A.setF i v default).size = max A.size (i + 1) := by
  rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
  · rw [setF_lt hi, size_set]
    exact (Nat.max_eq_left hi).symm
  · rw [setF_eq, size_push, Nat.max_eq_right (Nat.le_succ A.size)]
  · simp [setF, Nat.lt_asymm hi, setF_go_eq, size_append]
    have h_le : A.size ≤ i + 1 := by
      exact Nat.le_trans (Nat.le_of_lt hi) (Nat.le_succ _)
    rw [Nat.max_eq_right h_le, ← Nat.add_sub_assoc (Nat.le_of_lt hi),
      Nat.add_comm A.size i, Nat.add_sub_cancel]

-- CC: This is a rather weak lemma, but it's all that's needed for
--     theorems that want to prove facts about the maximum value of an array.
theorem mem_setF (A : Array α) (i : Nat) (v default : α) {a : α} :
    a ∈ (A.setF i v default) → a ∈ A ∨ a = default ∨ a = v := by
  intro ha
  rcases Nat.lt_trichotomy i A.size with (hi | rfl | hi)
  . simp [Array.setF_lt hi] at ha
    rw [← Array.mem_data] at ha
    rcases List.mem_or_eq_of_mem_set ha with (ha | rfl)
    · rw [Array.mem_data] at ha; exact Or.inl ha
    · right; right; rfl
  . simp at ha
    rcases ha with (h | h)
    · exact Or.inl h
    · exact Or.inr <| Or.inr h
  · simp [Array.setF_gt hi] at ha
    rcases ha with ((h | ⟨_, rfl⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr <| Or.inl rfl
      done
    · exact Or.inr <| Or.inr rfl

end Array
