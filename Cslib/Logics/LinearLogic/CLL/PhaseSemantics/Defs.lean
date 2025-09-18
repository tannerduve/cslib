/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Aesop
import Cslib.Logics.LinearLogic.CLL.Basic

/-!
# Phase semantics for CLL

In this file we define the phase semantics for classical linear logic, whose
syntax is defined in `Cslib.Logics.LinearLogic.CLL.Basic`.

## Main definitions

* `PhaseSpace`: a phase space is a commutative monoid with a bottom element.
* `Fact`: a fact is a subset of a phase space that is equal to its biorthogonal.
* `interp`: the interpretation of a proposition in a phase space.

## References

* [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]
-/

universe u v

namespace CLL

open Proposition

/--
A phase space is a pair (M, ⊥) where M is a commutative monoid and ⊥ is a subset of M.
-/
class PhaseSpace (M : Type u) extends CommMonoid M where
  bot : Set M

namespace PhaseSpace

/--
The implication of two sets in a phase space.
-/
def imp [PhaseSpace M] (X Y : Set M) : Set M := {m | ∀ x ∈ X, m * x ∈ Y}

@[inherit_doc] scoped infix:50 " ⊸ " => imp

/--
The orthogonal of a set in a phase space.
-/
def orthogonal [PhaseSpace M] (X : Set M) : Set M := X ⊸ bot

scoped postfix:max "⫠" => orthogonal

/--
A fact is a subset of a phase space that is equal to its biorthogonal
-/
structure Fact (M : Type u) [PhaseSpace M] where
  carrier : Set M
  closed  : carrier = (carrier⫠)⫠

instance [PhaseSpace M] : Coe (Fact M) (Set M) where
  coe F := F.carrier

def times [Monoid M] (A B : Set M) : Set M :=
  { z | ∃ m ∈ A, ∃ n ∈ B, z = m * n }

/--
The set of idempotents in a phase space
-/
def idems [PhaseSpace M] : Set M := {m | m * m = m}

def idemsIn [PhaseSpace M] (X : Set M) : Set M := {m | m ∈ idems ∧ m ∈ X}

/-- interpretation of `1` as a constant set (not via recursion) -/
def oneSet [PhaseSpace M] : Set M := ({1} : Set M)⫠⫠

/-- the set `I` of idempotents that “belong to 1” -/
def I [PhaseSpace M] : Set M := idemsIn (oneSet : Set M)

/--
The interpretation of a proposition in a phase space, given a valuation of atoms to facts.
-/
def interp [PhaseSpace M] (v : Atom → Fact M) : Proposition Atom → Set M
  | .atom a       => v a
  | .atomDual a   => (v a)⫠
  | .one          => oneSet
  | .zero         => (∅ : Set M)⫠⫠
  | .top          => (Set.univ : Set M)
  | .bot          => (PhaseSpace.bot : Set M)
  | .tensor X Y   => (times (interp v X) (interp v Y))⫠⫠
  | .parr    X Y   => (times ((interp v X)⫠) ((interp v Y)⫠))⫠
  | .oplus  X Y   => ((interp v X) ∪ (interp v Y))⫠⫠
  | .with   X Y   => (interp v X) ∩ (interp v Y)
  | .bang   X     => ((interp v X) ∩ I)⫠⫠
  | .quest  X     => (((interp v X)⫠) ∩ I)⫠

@[inherit_doc] scoped notation:max "⟦" P "⟧_" v:90 => interp v P

end PhaseSpace

end CLL
