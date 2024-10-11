/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: James Gallicchio, Cayden Codel
-/

theorem Int.neg_cast_le (n : Nat) : -(n : Int) ≤ 0 :=
  Int.neg_nonpos_of_nonneg (ofNat_zero_le n)

theorem Int.exists_nat_of_ge_zero {i : Int} : 0 ≤ i → ∃ (n : Nat), (n : Int) = i := by
  intro h
  cases i
  · rename Nat => n
    exact ⟨n, rfl⟩
  · contradiction

@[inline]
def Option.expectSome (err : Unit → ε) : Option α → Except ε α
| none => .error (err ())
| some a => .ok a

def Option.forIn [Monad m] (o : Option α) (b : β) (f : α → β → m (ForInStep β)) : m β := do
  match o with
  | none => return b
  | some a =>
  match ← f a b with
  | .done b => return b
  | .yield b => return b

instance : ForIn m (Option α) α where
  forIn := Option.forIn

structure NonemptyList (α) where
  hd : α
  tl : List α

@[inline]
def List.expectNonempty (err : Unit → ε) : List α → Except ε (NonemptyList α)
| [] => .error (err ())
| hd::tl => .ok ⟨hd,tl⟩

@[simp]
theorem Array.mkArray_zero (a : α) : Array.mkArray 0 a = #[] := by
  apply Array.ext'; simp [List.replicate]

theorem Array.mkArray_succ (n : Nat) (a : α) :
    Array.mkArray (n + 1) a = #[a] ++ (Array.mkArray n a) := by
  apply Array.ext'; simp [List.replicate]

theorem Array.mkArray_succ' (n : Nat) (a : α) :
    Array.mkArray (n + 1) a = (Array.mkArray n a).push a := by
  apply Array.ext'
  simp only [mkArray_data, List.replicate, push_data]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate]; exact ih

-- CC: This is a copy of a theorem of the same name in `Batteries.Data.Array`,
--     but that theorem is not marked as `@[simp]`. However, since its proof
--     is `by simp`, then it is probably superfluous.
@[simp]
theorem Array.mem_singleton : a ∈ #[b] ↔ a = b := by
  rw [List.toArray]
  simp [List.toArrayAux, Array.push, ← Array.mem_data]

@[simp]
theorem Array.mem_mkArray (n : Nat) (a b : α) : a ∈ Array.mkArray n b ↔ ((0 < n) ∧ a = b) := by
  induction n with
  | zero =>
    simp only [mkArray_zero, Nat.lt_irrefl, false_and, iff_false]
    exact not_mem_nil a
  | succ n ih =>
    simp [Array.mkArray_succ, ih]

@[simp]
theorem Array.mem_push (A : Array α) (a b : α) : a ∈ A.push b ↔ a ∈ A ∨ a = b := by
  simp only [push_eq_append_singleton, ← mem_data, append_data,
    data_toArray, List.mem_append, List.mem_singleton]

@[simp]
theorem Array.foldl_empty (f : β → α → β) (init : β) (start stop : Nat) :
    Array.foldl f init #[] start stop = init := by
  simp [foldl, foldlM, Id.run]
  by_cases h : stop = 0
  · simp [h, foldlM.loop]
  · simp [h]; simp [foldlM.loop]

@[simp]
theorem Array.foldl_nil (f : β → α → β) (init : β) (start stop : Nat) :
    Array.foldl f init { data := [] } start stop = init :=
  Array.foldl_empty f init start stop

@[simp]
theorem Array.foldl_cons (f : β → α → β) (init : β) (a : α) (as : List α) :
    Array.foldl f init { data := a :: as } 0 (size { data := a :: as }) =
      Array.foldl f (f init a) { data := as } 0 (size { data := as }) := by
  simp only [foldl_eq_foldl_data]; rfl

@[simp] theorem Array.foldl_append (f : β → α → β) (init : β) (A B : Array α) :
    Array.foldl f init (A ++ B) 0 (size (A ++ B)) =
      Array.foldl f (Array.foldl f init A 0 (size A)) B 0 (size B) := by
  have ⟨A⟩ := A
  have ⟨B⟩ := B
  simp only [foldl_eq_foldl_data, append_data]
  exact List.foldl_append _ _ _ _

@[simp] theorem Array.foldlM_empty {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (start stop : Nat) :
    Array.foldlM f init #[] start stop = pure init := by
  simp [foldlM, Id.run]
  by_cases h : stop = 0
  · simp [h, foldlM.loop]
  · simp [h]; simp [foldlM.loop]

@[simp] theorem Array.foldlM_nil {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (start stop : Nat) :
    Array.foldlM f init { data := [] } start stop = pure init :=
  Array.foldlM_empty f init start stop

@[simp] theorem Array.foldlM_trivial {m : Type v → Type w} [Monad m] (f : β → α → m β)
    (init : β) (as : Array α) (i : Nat) :
    as.foldlM f init i i = pure init := by
  simp [foldlM, Id.run]
  split <;> rename _ => hi
  · simp [foldlM.loop]
  · rw [foldlM.loop]
    simp at hi
    simp [Nat.not_lt_of_le (Nat.le_of_lt hi)]

@[simp] theorem Array.foldl_trivial (f : β → α → β)
    (init : β) (as : Array α) (i : Nat) :
    as.foldl f init i i = init := by
  simp [foldl, Id.run]
