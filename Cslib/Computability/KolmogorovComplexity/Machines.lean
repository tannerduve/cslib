/-
Machines.lean

Universal machines and (plain) Kolmogorov complexity, relativized to oracles.

This file intentionally does *not* try to prove anything like:
- "U is computable"
- "invariance theorem"
- "prefix-freeness", etc.

It just sets up the objects so you can talk about KC^A cleanly.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Computability.Partrec
import Cslib.Computability.KolmogorovComplexity.Encoding
-- The above file was ported from the working directory on Mathlib.Computability
import Cslib.Computability.KolmogorovComplexity.BinSeq

-- import BinSeq

import Mathlib.Data.Part
import Mathlib.Logic.Encodable.Basic

namespace AlgorithmicRandomness

open Part

/-- An indexed family of partial oracles. -/
abbrev OracleFam (α : Type) := α → ℕ →. ℕ

/-- A single oracle (not a family). -/
abbrev Oracle := ℕ →. ℕ

/-- View a single oracle as a family indexed by `Unit`. -/
def asFam (O : Oracle) : OracleFam Unit := fun _ => O

-- /-- A total set oracle: query membership and return `1/0`. -/
-- def setOracle (A : Set ℕ) : Oracle :=
--   fun n => Part.some (if n ∈ A then 1 else 0)

/--
Interpret a natural number `e` as a `codeo`-program (via `decodeCodeo`)
and run it relative to oracle family `F`.
-/
noncomputable def Φ {α : Type} [Primcodable α]
  (F : OracleFam α) (e : ℕ) : ℕ →. ℕ :=
  evalo F (decodeCodeo e)

/-- Universal numeric machine relative to oracle family `F`. -/
noncomputable def Uₙ {α : Type} [Primcodable α]
  (F : OracleFam α) (e : ℕ) : ℕ →. ℕ :=
  fun x => (Φ F e) x

/-- Encode a `BinSeq` as a natural. -/
abbrev binEnc (σ : BinSeq) : ℕ := Encodable.encode σ

/-- Decode a natural to `BinSeq` (failure = divergence). -/
def binDec (n : ℕ) : Part BinSeq :=
  match BinSeq.decode n with
  | Option.some σ => Part.some σ
  | .none   => Part.none

/--
Universal machine on binary sequences.

Program `p` is interpreted as `Encodable.encode p`, then decoded to a `codeo`
using `decodeCodeo`, and executed via `evalo`. Input/output are encoded/decoded
using the `Encodable BinSeq` instance.
-/
noncomputable def U {α : Type} [Primcodable α]
  (F : OracleFam α) (p : BinSeq) : BinSeq →. BinSeq :=
  fun σ => (evalo F (decodeCodeo (binEnc p)) (binEnc σ)).bind binDec

/-
Plain Kolmogorov complexity (relativized).

You asked for: no `WithTop`. If nothing shorter outputs `x`, return `length x`.

So we define KC as the shortest program length among those that output `x`,
bounded above by `x.length`, and defaulting to `x.length`.
-/

/-- Does there exist a program of length `n` producing `x` (on empty input)? -/
def Produces {α : Type} [Primcodable α]
  (F : OracleFam α) (x : BinSeq) (n : Nat) : Prop :=
  ∃ p : BinSeq, p.length = n ∧ U F p BinSeq.empty = Part.some x

/-- lengths of programs producing `x` on empty input -/
def goodLengths {α : Type} [Primcodable α] (F : OracleFam α) (x : BinSeq) : Set Nat :=
  { n | ∃ p : BinSeq, p.length = n ∧ U F p BinSeq.empty = Part.some x }

/--
Plain KC relative to `F`.

We take the least `n` in `goodLengths F x`, but if none exist we return `x.length`.
(So the value is always a natural, never `⊤`.)
-/
noncomputable def plainKC {α : Type} [Primcodable α]
  (F : OracleFam α) (x : BinSeq) : Nat :=
by
  classical
  let S : Set Nat := goodLengths F x
  by_cases h : S.Nonempty
  · sorry
    -- exact sInf S
  · exact x.length


/-- Plain KC relative to a single oracle. -/
noncomputable def plainKC₁ (O : Oracle) (x : BinSeq) : Nat :=
  plainKC (asFam O) x

end AlgorithmicRandomness
