/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Aesop
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

import Mathlib.Order.Closure
import Mathlib.Algebra.Group.Pointwise.Set.Basic
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
open scoped Pointwise

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
The orthogonal of a set is antitone
-/
lemma orth_antitone [PhaseSpace M] {X Y : Set M} (hXY : X ⊆ Y) :
    Y⫠ ⊆ X⫠ := by
  intro m hm x hx
  exact hm x (hXY hx)

/--
The biorthogonal operator is extensive
-/
lemma subset_biorthogonal [PhaseSpace M] (X : Set M) : X ⊆ X⫠⫠ := by
  intro x hx n hn
  simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hn x hx

/--
The triple-orthogonal of a set is equal to the orthogonal
-/
lemma triple_orth [PhaseSpace M] (X : Set M) : X⫠⫠⫠ = X⫠ := by
  apply le_antisymm
  · intro m hm x hxX
    have hx' : x ∈ (X⫠)⫠ := by
      intro y hy
      simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hy x hxX
    exact hm x hx'
  · apply subset_biorthogonal (X := X⫠)

/-- The biorthogonal closure operator on `Set M`. -/
def biorthogonalClosure [PhaseSpace M] : ClosureOperator (Set M) := {
  toFun := fun X => X⫠⫠
  monotone' := by
    intro X Y hXY m hm n hnY
    have hnX : n ∈ X⫠ := by
      intro x hxX
      exact hnY x (hXY hxX)
    exact hm n hnX
  le_closure' := by
    intro X x hx n hn
    simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hn x hx
  idempotent' := by
    intro X
    simp [triple_orth (X := X⫠)]
}

lemma univ_closed [PhaseSpace M] : (Set.univ : Set M) = (Set.univ⫠)⫠ := by
  apply le_antisymm
  · exact subset_biorthogonal (X := (Set.univ : Set M))
  · intro m hm
    exact Set.mem_univ m
/--
A fact is a subset of a phase space that is equal to its biorthogonal
-/
structure Fact (M : Type u) [PhaseSpace M] where
  carrier : Set M
  closed  : carrier = (carrier⫠)⫠

/--
A set is a fact if and only if it is of the form `Y⫠` for some `Y`.
-/
lemma fact_iff_exists_orth [PhaseSpace M] (X : Set M) :
    X = X⫠⫠ ↔ ∃ Y : Set M, X = Y⫠ := by
  constructor
  · intro hX
    refine ⟨X⫠, ?_⟩
    exact hX
  · rintro ⟨Y, rfl⟩
    simp [triple_orth (X := Y)]

instance [PhaseSpace M] : Coe (Fact M) (Set M) where
  coe F := F.carrier


/--
The set of idempotents in a phase space
-/
def idems [Monoid M] : Set M := {m | m * m = m}

def idemsIn [Monoid M] (X : Set M) : Set M := {m | m ∈ idems ∧ m ∈ X}

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
  | .tensor X Y   => ((interp v X) * (interp v Y))⫠⫠
  | .parr    X Y   => (((interp v X)⫠) * ((interp v Y)⫠))⫠
  | .oplus  X Y   => ((interp v X) ∪ (interp v Y))⫠⫠
  | .with   X Y   => (interp v X) ∩ (interp v Y)
  | .bang   X     => ((interp v X) ∩ I)⫠⫠
  | .quest  X     => (((interp v X)⫠) ∩ I)⫠

@[inherit_doc] scoped notation:max "⟦" P "⟧" v:90 => interp v P

end PhaseSpace

end CLL
