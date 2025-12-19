/-
BinSeq.lean

Small utilities for finite binary strings.
Kept separate so Machines.lean can stay focused on machines/complexity.
-/

import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Basic

namespace AlgorithmicRandomness

/-- Finite binary sequences. -/
inductive BinSeq : Type
  | empty : BinSeq
  | cons (b : Bool) (σ : BinSeq) : BinSeq
deriving Repr, DecidableEq, Inhabited

namespace BinSeq

/-- Length of a binary sequence. -/
def length : BinSeq → Nat
  | empty    => 0
  | cons _ σ => σ.length + 1

/-- Append two binary sequences. -/
def append : BinSeq → BinSeq → BinSeq
  | empty,      τ => τ
  | cons b σ, τ => cons b (append σ τ)

instance : Append BinSeq := ⟨append⟩

@[simp] theorem empty_append (τ : BinSeq) : empty ++ τ = τ := rfl

@[simp] theorem cons_append (b : Bool) (σ τ : BinSeq) :
    (cons b σ) ++ τ = cons b (σ ++ τ) := rfl

/-- Map a function over bits. -/
def map (f : Bool → Bool) : BinSeq → BinSeq
  | empty    => empty
  | cons b σ => cons (f b) (map f σ)

/-- Reverse a binary sequence. -/
def reverse : BinSeq → BinSeq
  | empty    => empty
  | cons b σ => (reverse σ) ++ cons b empty

/-- A convenience constructor from a list of booleans. -/
def ofList : List Bool → BinSeq
  | []      => empty
  | b :: t  => cons b (ofList t)

/-- Convert back to a list (handy for debugging/printing). -/
def toList : BinSeq → List Bool
  | empty    => []
  | cons b σ => b :: toList σ

@[simp] theorem length_empty : (empty : BinSeq).length = 0 := rfl
@[simp] theorem length_cons (b : Bool) (σ : BinSeq) :
    (cons b σ).length = σ.length + 1 := rfl

open Nat

def encode : BinSeq → Nat
  | empty      => 0
  | cons false σ => 2 * encode σ + 1
  | cons true  σ => 2 * encode σ + 2

def decode : Nat → Option BinSeq
  | 0 => some empty
  | n + 1 =>
      let k := n / 2
      match n % 2 with
      | 0 => cons true  <$> decode k
      | _ => cons false <$> decode k
termination_by n => n
decreasing_by
  -- goal: k < n+1 where k = n/2 (in the `n+1` branch)
  -- simp turns the goal into something about Nat.div_lt_self
  simp_wf
  · cases n
    · simp
    · grind

lemma encodek : ∀ σ, decode (encode σ) = some σ
  | empty => sorry
  | cons false σ =>
      sorry
  | cons true σ =>
      sorry
instance : Encodable BinSeq :=
{ encode   := encode,
  decode   := decode,
  encodek  := encodek
}


end BinSeq

end AlgorithmicRandomness
