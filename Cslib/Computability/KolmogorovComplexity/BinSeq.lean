/-
BinSeq.lean

Small utilities for finite binary strings.
Kept separate so Machines.lean can stay focused on machines/complexity.
-/

import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace AlgorithmicRandomness

/-- Finite binary sequences. -/
abbrev BinSeq := List Bool
namespace BinSeq

open Nat

def encode : BinSeq → Nat
  | []      => 0
  | b :: σ => 2 * encode σ + (if b then 2 else 1)

def decode : Nat → Option BinSeq
  | 0 => some []
  | n + 1 =>
    if (n + 1) % 2 = 1 then List.cons false <$> (decode ((n + 1) / 2))
    else List.cons true <$> (decode ((n + 1) / 2 - 1))

lemma decode_encode (σ : BinSeq) :
                            decode (encode σ) = σ := by
  induction σ with
  | nil =>
    simp [decode, encode];
  | cons b σ ih =>
    by_cases hb : b;
    · have h_even :
      decode (2 * (encode σ) + 2) = List.cons true <$> (decode ((2 * (encode σ) + 2) / 2 - 1)) := by
        rw [decode]
        grind
      simp_all only [zero_lt_succ, add_div_right, mul_div_right, Nat.add_one_sub_one,
        Option.map_eq_map, Option.map_some]
      simp [encode, h_even]
    · have h_ofNat_odd : decode (2 * (encode σ) + 1) = List.cons false <$> (decode (encode σ)) := by
        rw [ decode ]
        grind
      aesop

instance : Encodable BinSeq := ⟨encode, decode, decode_encode⟩

end BinSeq

end AlgorithmicRandomness
