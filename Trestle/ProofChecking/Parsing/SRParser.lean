/-
Copyright (c) 2024 The Trestle Contributors.
Released under the Apache License v2.0; see LICENSE for full text.

Authors: Cayden Codel
-/

import Trestle.ProofChecking.Parsing.Defs
import Trestle.ProofChecking.Data.AsciiIterator

/-!

LSR file parsing.

-/

namespace Trestle

namespace SRParser

open Parsing

variable {CNF : Type _} [Formula CNF] [Inhabited CNF]

@[specialize]
def parseClause (maxVar : Nat) (F : CNF) (arr : ByteArray') (iter : USize) : Except Unit (CNF × USize) :=
  let size := arr.val.size.toUSize
  let rec loop (F : CNF) (iter : USize) : Except Unit (CNF × USize) :=
    if hi : iter < size then
      let ⟨atom, iter'⟩ := ByteArray.readInt arr iter

      if h_atom : atom = 0 then
        .ok (Formula.commitClause F, iter')
      else
        if atom.natAbs > maxVar then
          -- Out of bounds variable
          .error ()
        else
          have : (arr.val.size.toUSize - iter').toNat < (arr.val.size.toUSize - iter).toNat := by
            have := ByteArray.readInt_iter_gt hi
            sorry
            done
          loop (Formula.addLiteral F ⟨atom, h_atom⟩) iter'
    else
      .error ()
  termination_by arr.val.size.toUSize - iter

  loop F iter

--@[inline, always_inline, specialize]
@[specialize]
partial def parseClauses (nvars ncls : Nat) (F : CNF) (arr : ByteArray') (iter : USize) : Except String CNF :=
  let size := arr.val.size.toUSize
  let rec loop (F : CNF) (iter : USize) : Except String (CNF × USize) :=
    let iter := ByteArray.ws arr iter
    if _ : iter < size then
      match parseClause nvars F arr iter with
      | .error _ => .error "Clause parsing error"
      | .ok ⟨F, iter⟩ => loop F iter
    else
      .ok (F, iter)

  match loop F iter with
  | .ok (F, _) =>
    if Formula.size F != ncls then
      throw s!"Expected {ncls} clauses, but found {Formula.size F}"
    else
      .ok F
  | .error str => throw str

--@[inline]
def parseHeader (arr : ByteArray') (iter : USize) : Except String (Nat × Nat × USize) :=
  -- Assumes that the first two non-whitespace tokens are "p" and "cnf"
  let iter := ByteArray.skip arr iter
  let iter := ByteArray.skip arr iter

  -- Now parse two nats
  let ⟨nVars, iter⟩ := ByteArray.readNat arr iter
  let ⟨nCls, iter⟩ := ByteArray.readNat arr iter

  if nVars = 0 || nCls = 0 || iter >= arr.val.size.toUSize then
    throw s!"Invalid header: {nVars}, {nCls}, or iter out of bounds"
  else
    .ok (nVars, nCls, iter)

@[specialize]
def parseFormula (arr : ByteArray') (F : CNF) : Except String (CNF × Nat) :=
  match parseHeader arr 0 with
  | .error str => throw str
  | .ok (nvars, ncls, iter) =>
    match parseClauses nvars ncls F arr iter with
    | .ok F => .ok (F, nvars)
    | .error str => throw str

-- CC: Because the parse line is called at top-level, it's okay for this to be Except.
-- Returns the line id, the updated formula (with the candidate clause loaded), and the line
@[specialize]
partial def parseLSRAdditionLine (F : CNF) (arr : ByteArray') (iter : USize) : Except String (USize × CNF × SRAdditionLine) :=
  -- Assume that `iter` is after the line ID, and that there is no `'d'`.
  -- Parse the first integer to get the pivot (or 0 for the empty clause)
  let size := arr.val.size.toUSize
  let line := SRAdditionLine.new
  let ⟨pivot, iter⟩ := ByteArray.readInt arr iter
  let st :=
    if hp : pivot = 0 then
      ParsingState.mk .upHints F line
    else
      ParsingState.mk .clause (Formula.addLiteral F ⟨pivot, hp⟩) line

  let rec loop (st : ParsingState CNF) (iter : USize) : Except String (USize × CNF × SRAdditionLine) :=
    if _ : iter < size then
      let ⟨atom, iter⟩ := ByteArray.readInt arr iter
      have ⟨mode, F, line⟩ := processSRAtom atom pivot st
      match mode with
      | .err str => throw str
      | .lineDone => .ok (iter, F, line)
      | _ => loop ⟨mode, F, line⟩ iter
    else
      throw "Line ended early"

  loop st iter

@[specialize]
partial def parseDeletionLine (arr : ByteArray') (iter : USize) : Except String (Array Nat × USize) :=
  let iter := ByteArray.ws arr iter
  let size := arr.val.size.toUSize

  let rec loop (acc : Array Nat) (iter : USize) : Except String (Array Nat × USize) :=
    if _ : iter < size then
      let ⟨atom, iter⟩ := ByteArray.readNat arr iter
      if atom = 0 then
        .ok ⟨acc, iter⟩
      else
        loop (acc.push (atom - 1)) iter
    else
      throw "Line ended early"

  loop #[] iter


#exit

--------------------------------------------------------------------------------

def undoBinaryMapping (x : UInt64) : Int :=
  if x &&& 1 = 1 then
    ((((x >>> 1).toNat) : Int) * -1)
  else
    (((x >>> 1).toNat) : Int)

-- CC: This version is an attempt to get totality
/-
def readBinaryToken (A : ByteArray) (index : Nat) : Int × { i : Nat // i > index } :=
  let rec go (i : Nat) (acc : UInt64) (shift : UInt64) : Int × { idx : Nat // idx > i } :=
    if hi : i < A.size then
      let atom : UInt8 := A.get ⟨i, hi⟩
      let acc' : UInt64 := acc ||| ((atom &&& 127).toUInt64 <<< shift)
      if atom &&& 128 != 0 then
        match go (i + 1) acc' (shift + 7) with
        | ⟨a, ⟨b, hb⟩⟩ => ⟨a, ⟨b, Nat.le_of_succ_le hb⟩⟩
      else
        ⟨undoBinaryMapping acc', ⟨A.size, hi⟩⟩
    else
      ⟨undoBinaryMapping acc, ⟨i + 1, Nat.lt_succ_self _⟩⟩
  termination_by A.size - i
  go index 0 0
-/

-- Int is result, Nat is cached index into A
partial def readBinaryToken (A : ByteArray) (index : Nat) : Int × Nat :=
  let rec go (i : Nat) (acc : UInt64) (shift : UInt64) : Int × Nat :=
    if hi : i < A.size then
      let atom : UInt8 := A.get ⟨i, hi⟩
      let acc' : UInt64 := acc ||| ((atom &&& 127).toUInt64 <<< shift)
      if atom &&& 128 != 0 then
        go (i + 1) acc' (shift + 7)
      else
        ⟨undoBinaryMapping acc', i + 1⟩
    else
      ⟨undoBinaryMapping acc, A.size⟩
  let ⟨res, idx⟩ := go index 0 0
  ⟨res, idx⟩

-- Bool: found a 0
-- Nat: updated index
partial def parseLSRDeletionLineBinary (A : ByteArray) (index : Nat) : Bool × Nat × SRDeletionLine :=
  let rec go (i : Nat) (acc : Array Nat) : Bool × Nat × SRDeletionLine :=
    if i < A.size then
      let (x, j) := readBinaryToken A i
      if x = 0 then
        ⟨true, j, SRDeletionLine.mk acc⟩
      else
        go j (acc.push (x.natAbs - 1))
    else
      ⟨false, A.size, SRDeletionLine.mk acc⟩
  go index #[]

instance : Inhabited (Nat × ParsingState CNF) :=
  ⟨⟨0, ParsingState.mk .clause none (Formula.empty) (SRAdditionLine.new)⟩⟩

@[specialize]
partial def parseLSRAdditionLineBinary (F : CNF) (A : ByteArray)
    (index : Nat) (pivot : Option ILit) : Nat × ParsingState CNF :=
  let rec go (i : Nat) (st : ParsingState CNF) : Nat × ParsingState CNF :=
    have : Inhabited (Nat × ParsingState CNF) := by infer_instance
    if i < A.size then
      let (n, j) := readBinaryToken A i
      let st := processSRAtom n st
      match st.mode with
      | .err _ => (j, st)
      | .lineDone => (j, st)
      | _ => go j st
    else
      ⟨A.size, st⟩

  let newLine := SRAdditionLine.new
  match pivot with
  | none => go index (ParsingState.mk .upHints none F newLine)
  | some p => go index (ParsingState.mk .clause (some p) (Formula.addLiteral F p) newLine)

-- First nat is cached index into arr, second is ID of new clause to add
partial def parseLSRLineBinary (F : CNF) (A : ByteArray) (index : Nat)
    : Except String (Nat × Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine)) :=
  if hi : index + 1 < A.size then
    -- Check if we have an addition line or a deletion line
    let lineStart : UInt8 := A.get ⟨index, Nat.lt_of_succ_lt hi⟩
    let ⟨lineId, index⟩ := readBinaryToken A (index + 1)
    if lineId < 0 then error "Negative line ID" else

    -- Addition line
    if lineStart = 1 then
      let F := Formula.commitClauseUntil F (lineId.natAbs - 1)

      -- Check if we have a pivot
      if index < A.size then
        let ⟨pivot, index⟩ := readBinaryToken A index
        let ⟨index, st⟩ :=
          if hp : pivot = 0 then
            parseLSRAdditionLineBinary F A index none
          else
            parseLSRAdditionLineBinary F A index (some ⟨pivot, hp⟩)
        match st.mode with
        | .err str => throw str
        | .lineDone => ok (index, lineId.natAbs, st.F, .inl st.line)
        | _ => error "Addition line didn't end with 0"
      else
        error "Line ended early"
    else if lineStart = 2 then
      match parseLSRDeletionLineBinary A index with
      | ⟨true, index, line⟩ => ok (index, lineId.natAbs, F, .inr line)
      | ⟨false, _, _⟩ => error "Deletion line didn't end with 0"
    else
      error "Start of line wasn't addition (1) or deletion (2)"

  else
    error "No more string!"

#exit

/- Correctness -/
-- parseLSRLine (F : CNF) (s : String) : Except String (Nat × CNF × (SRAdditionLine ⊕ SRDeletionLine))
-- CC: We trust that parsing is successful, so we only prove that there
--     exists a clause that `F` models on a successful parse
open RangeArray in
theorem parseLSRLine_ok_inl {F F' : RangeArray ILit} {s : String} {id : Nat} {addLine : SRAdditionLine} {Ls : List (Option (List ILit))} :
  parseLSRLine F s = Except.ok (id, F', Sum.inl addLine) →
    models F Ls [] →
    ∃ C, models F' (Ls ++ (List.replicate (id - Ls.length) none)) C := by
  sorry
  done

theorem parseLSRLine_ok_inr {F F' : RangeArray ILit} {s : String} {id : Nat} {delLine : SRDeletionLine} :
    parseLSRLine F s = Except.ok (id, F', Sum.inr delLine) → F = F' := by
  sorry
  done

end SRParser
