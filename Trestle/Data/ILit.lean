/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Wojciech Nawrocki, Cayden Codel
-/

/-

Implementations of DIMACS literals and variables.

-/

namespace Trestle

-- TODO: We could add an implementation type that uses `UInt64` or `USize` instead,
--       since almost all CNF instances will use "small" variable names.

/--
  The implementation type of DIMACS variables (hence the "I" in `IVar`).

  In DIMACS, variables are represented by strictly positive integers.
  We attach the positivity-hypothesis as a subtype here.

  This type is the exact same as the one for `PNat` in Mathlib
  (see [Data.PNat.Defs.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/PNat/Defs.lean)).
  To avoid a dependence on Mathlib, we re-define it here,
  and then provide a theorem in `trestle` that the two types are the same.
-/
def IVar := { n : Nat // 0 < n }
  deriving DecidableEq, Repr

/--
  The implementation type of DIMACS literals (hence the "I" in `ILit`).

  In DIMACS, literals are non-zero integers, with negative numbers variables with an optional negation.
  We represent them as integers, with the invariant that they are non-zero.
-/
def ILit := { i : Int // i ≠ 0 }
  deriving DecidableEq, Repr

namespace IVar

instance instInhabited : Inhabited IVar := ⟨⟨1, by decide⟩⟩

def toString : IVar → String
  | ⟨n, _⟩ => s!"{n}"

instance instToString : ToString IVar where
  toString := toString

instance instHashable : Hashable IVar where
  hash v := hash v.val

instance instOrd : Ord IVar where
  compare a b := compare a.val b.val

instance instCoeNat : Coe IVar Nat where
  coe v := v.val

protected def max : IVar → IVar → IVar
  | ⟨v₁, _⟩, ⟨v₂, _⟩ => ⟨max v₁ v₂, by
      have := Nat.le_max_left v₁ v₂
      have := Nat.le_max_right v₁ v₂
      omega
    ⟩

def toPosILit : IVar → ILit
  | ⟨n, hn⟩ => ⟨Int.ofNat n, by exact Int.natAbs_pos.mp hn⟩

def toNegILit : IVar → ILit
  | ⟨n, hn⟩ => ⟨-Int.ofNat n, by
    intro h_con
    rw [Int.neg_eq_zero] at h_con
    revert h_con
    exact Int.natAbs_pos.mp hn⟩

instance instCoeIVar : Coe IVar ILit where
  coe v := toPosILit v

/-! # index -/

/--
  Converts an `IVar` into a 0-indexed `Nat`.

  DIMACS variables are 1-indexed, but arrays are 0-indexed,
  so `index` subtracts one and does the coercion.
-/
@[inline, always_inline]
def index (v : IVar) : Nat := v - 1

/-- Converts a 0-indexed `Nat` into an `IVar`.  -/
@[inline, always_inline]
def ofIndex (n : Nat) : IVar := ⟨n + 1, by omega⟩

end IVar

--------------------------------------------------------------------------------

namespace ILit

instance instInhabited : Inhabited ILit := ⟨1, by decide⟩

instance instHashable : Hashable ILit where
  hash v := hash v.val

instance instOrd : Ord ILit where
  compare a b := compare a.val b.val

instance instCoeInt : Coe ILit Int where
  coe v := v.val

def toString : ILit → String
  | ⟨l, _⟩ => s!"{l}"

instance : ToString ILit where
  toString := toString

def toIVar : ILit → IVar
  | ⟨l, hl⟩ => ⟨l.natAbs, Int.natAbs_pos.mpr hl⟩

instance instCoeToIVar : Coe ILit IVar where
  coe v := toIVar v

def ofIVar : IVar → ILit
  | ⟨n, hn⟩ => ⟨Int.ofNat n, by exact Int.natAbs_pos.mp hn⟩

instance instCoeOfIVar : Coe IVar ILit where
  coe v := ofIVar v

def toNat : ILit → Nat
  | ⟨l, _⟩ => l.natAbs

/-- Returns `true` iff the literal is positive. -/
def polarity : ILit → Bool
  | ⟨l, _⟩ => l > 0

def negate : ILit → ILit
  | ⟨l, _⟩ => ⟨-l, by
    intro h
    have := Int.neg_eq_zero.mp h
    contradiction⟩

instance instNeg : Neg ILit where
  neg := negate

/-! # index -/

/--
  Converts an `ILit` into a 0-indexed `Nat`.

  DIMACS literals are 1-indexed (ignoring sign), but arrays are 0-indexed,
  so `index` subtracts one and does the coercion.
-/
@[inline, always_inline]
def index (l : ILit) : Nat := l.val.natAbs - 1

/-- Converts a 0-indexed `Nat` into an `ILit`. -/
@[inline, always_inline]
def ofIndex (n : Nat) : ILit := ⟨n + 1, by omega⟩

end ILit

end Trestle
