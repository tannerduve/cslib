/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Mathlib.Control.Monad.Writer

/-!
# Time monad

This file defines a simple monad `TimeM` that pairs a value with a natural number
representing an accumulated time/cost. As plain types it is isomorphic to `Writer Nat`.

## Main definitions

- `TimeM`          : computations with a time component
- `TimeM.equivWriter` : equivalence with `Writer Nat`
-/

namespace Cslib

universe u

/-- A computation that returns a value of type `α` together with an accumulated
time cost (a natural number). -/
structure TimeM (α : Type u) where
  /-- The result of the computation. -/
  val : α
  /-- The accumulated time cost. -/
  time : Nat

namespace TimeM

variable {α β : Type u}

/-- Return a value with zero time cost. -/
def pure (a : α) : TimeM α :=
  ⟨a, 0⟩

/-- Sequence two computations, adding their time components. -/
def bind (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.val
  ⟨r.val, m.time + r.time⟩

instance : Monad TimeM where
  pure := pure
  bind := bind

/-- Construct a value that costs `c` units of time. -/
def tick (a : α) (c : Nat := 1) : TimeM α :=
  ⟨a, c⟩

@[simp] theorem time_of_pure (a : α) : (pure a).time = 0 := rfl

@[simp] theorem time_of_bind (m : TimeM α) (f : α → TimeM β) :
    (bind m f).time = m.time + (f m.val).time := rfl

@[simp] theorem time_of_tick (a : α) (c : Nat) : (tick a c).time = c := rfl

@[simp] theorem val_bind (m : TimeM α) (f : α → TimeM β) :
    (bind m f).val = (f m.val).val := rfl

/-- `TimeM` is (definitionally) the same as the writer monad `Writer Nat`. -/
abbrev WriterNat (α : Type) := WriterT Nat Id α

/-- Equivalence between `TimeM α` and `Writer Nat α` as plain types. -/
def equivWriter (α : Type) : TimeM α ≃ WriterNat α where
  toFun m := (m.val, m.time)
  invFun w := ⟨w.1, w.2⟩
  left_inv m := by cases m; rfl
  right_inv w := by cases w; rfl

@[simp] lemma equivWriter_toFun {α : Type} (m : TimeM α) :
    (equivWriter α m : WriterNat α) = (m.val, m.time) := rfl

@[simp] lemma equivWriter_invFun {α : Type} (w : WriterNat α) :
    (equivWriter α).invFun w = TimeM.mk w.1 w.2 := rfl

end TimeM

end Cslib
