/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Data.Set.Basic
import Mathlib.Order.Closure
import Cslib.Logics.LinearLogic.CLL.Basic

/-!
# Phase semantics for Classical Linear Logic

This file develops the phase semantics for Classical Linear Logic (CLL), providing an
algebraic interpretation of linear logic propositions in terms of phase spaces.

Phase semantics is a denotational semantics for linear logic where
propositions are interpreted as subsets of a commutative monoid, and logical operations
correspond to specific set-theoretic operations.

## Main definitions

* `PhaseSpace`: A commutative monoid equipped with a distinguished subset ⊥
* `PhaseSpace.imp`: Linear implication `X ⊸ Y` between sets in a phase space
* `PhaseSpace.orthogonal`: The orthogonal `X⫠` of a set X
* `PhaseSpace.isFact`: A fact is a set that equals its biorthogonal closure
* `Fact`: The type of facts in a phase space
* `PhaseSpace.interp`: Interpretation of CLL propositions in a phase space
* `PhaseSpace.interp₁`: Interpretation of CLL propositions *as facts* in a phase space

## Main results

* `PhaseSpace.triple_orth`: The triple orthogonal equals the orthogonal (X⫠⫠⫠ = X⫠)
* `PhaseSpace.biorthogonalClosure`: The biorthogonal operation forms a closure operator
* `PhaseSpace.interp_closed`: Every interpreted proposition is a fact
* `PhaseSpace.imp_isFact_of_fact`: Linear implication preserves the fact property

## TODO
- Soundness theorem
- Completeness theorem

## References

* [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]
-/

universe u v

namespace CLL

open Proposition
open scoped Pointwise
open Set

/--
A phase space is a commutative monoid M equipped with a distinguished subset ⊥.
This forms the algebraic foundation for interpreting linear logic propositions.
-/
class PhaseSpace (M : Type u) extends CommMonoid M where
  /-- The distinguished subset ⊥ used to define orthogonality -/
  bot : Set M

namespace PhaseSpace

-- ## Basic operations

/--
Linear implication `X ⊸ Y` in a phase space: the set of elements m such that
for all x ∈ X, we have m * x ∈ Y.
-/
def imp [PhaseSpace M] (X Y : Set M) : Set M := {m | ∀ x ∈ X, m * x ∈ Y}

@[inherit_doc] scoped infix:50 " ⊸ " => imp

/--
The orthogonal `X⫠` of a set X: the set of elements that map X into ⊥ under multiplication.
-/
def orthogonal [PhaseSpace M] (X : Set M) : Set M := X ⊸ bot

@[inherit_doc] scoped postfix:max "⫠" => orthogonal

-- ## Properties of orthogonality

/--
The orthogonal operation is antitone: if X ⊆ Y then Y⫠ ⊆ X⫠.
-/
lemma orth_antitone [PhaseSpace M] {X Y : Set M} (hXY : X ⊆ Y) :
    Y⫠ ⊆ X⫠ := by
  intro m hm x hx
  exact hm x (hXY hx)

/--
The biorthogonal operation is extensive: X ⊆ X⫠⫠ for any set X.
-/
lemma orthogonal_extensive [PhaseSpace M] (X : Set M) : X ⊆ X⫠⫠ := by
  intro x hx n hn
  simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hn x hx

/--
The triple orthogonal equals the orthogonal: X⫠⫠⫠ = X⫠.
-/
lemma triple_orth [PhaseSpace M] (X : Set M) : X⫠⫠⫠ = X⫠ := by
  apply le_antisymm
  · intro m hm x hxX
    have hx' : x ∈ (X⫠)⫠ := by
      intro y hy
      simpa [orthogonal, imp, Set.mem_setOf, mul_comm] using hy x hxX
    exact hm x hx'
  · apply orthogonal_extensive

/--
The biorthogonal closure operator on sets in a phase space.
-/
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
    simp [triple_orth]
}

-- ## Facts

/--
A fact is a subset of a phase space that equals its biorthogonal closure.
-/
def isFact [PhaseSpace M] (X : Set M) : Prop := X = X⫠⫠

/--
The type of facts in a phase space.
-/
abbrev Fact (M : Type u) [PhaseSpace M] := { X : Set M // isFact X }

instance [PhaseSpace M] : Coe (Fact M) (Set M) := ⟨Subtype.val⟩

lemma coe_mk [PhaseSpace M] {X : Set M} {h : isFact X} :
    ((⟨X, h⟩ : Fact M) : Set M) = X := rfl

@[simp] lemma closed [PhaseSpace M] (F : Fact M) : isFact (F : Set M) := F.property

@[simp] lemma top_isFact [PhaseSpace M] :
    isFact (univ : Set M) := by
  rw [isFact]; symm
  simpa [top_eq_univ]
    using ClosureOperator.closure_top CLL.PhaseSpace.biorthogonalClosure

/--
A set is a fact if and only if it is the orthogonal of some set
-/
lemma fact_iff_exists_orth [PhaseSpace M] (X : Set M) :
    isFact X ↔ ∃ Y : Set M, X = Y⫠ := by
  constructor
  · intro hX
    refine ⟨X⫠, ?_⟩
    exact hX
  · rintro ⟨Y, rfl⟩
    simp [isFact, triple_orth]

/--
If Y is a fact, then X ⊸ Y is also a fact
-/
lemma imp_isFact_of_fact [PhaseSpace M] (X Y : Set M) (hY : isFact Y) :
    isFact (X ⊸ Y) := by
  have hXY : (X ⊸ Y) = (X * Y⫠)⫠ := by
    ext m
    constructor
    · intro hm z hz
      rcases hz with ⟨x, hxX, y, hyYperp, rfl⟩
      have hmx : m * x ∈ Y := hm x hxX
      have : y * (m * x) ∈ bot := hyYperp (m * x) (by simpa using hmx)
      simpa [mul_left_comm, mul_comm, mul_assoc] using this
    · intro hm x hxX
      have hxYbi : m * x ∈ Y⫠⫠ := by
        intro y hy
        have : m * (x * y) ∈ bot := hm (x * y) ⟨x, hxX, y, hy, rfl⟩
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      rw [hY]; exact hxYbi
  simp [isFact, hXY, triple_orth]

/--
Linear implication between a set and a fact, yielding a fact.
-/
def Fact.imp [PhaseSpace M] (X : Set M) (Y : Fact M) : Fact M :=
  ⟨ X ⊸ Y, imp_isFact_of_fact X Y Y.property ⟩

lemma isFact_iff_closed [PhaseSpace M] (X : Set M) :
  isFact X ↔ biorthogonalClosure.IsClosed X := by
  constructor <;> (intro; simp only [isFact, biorthogonalClosure]; symm; assumption)

/--
Arbitrary intersections of facts are facts.
-/
lemma sInf_isFact [PhaseSpace M] {S : Set (Set M)}
    (H : ∀ X ∈ S, isFact X) : isFact (sInf S) := by
  have H' : ∀ X ∈ S, biorthogonalClosure.IsClosed X :=
    fun X hX => (isFact_iff_closed X).1 (H X hX)
  have : biorthogonalClosure.IsClosed (sInf S) :=
    ClosureOperator.sInf_isClosed (c := biorthogonalClosure) H'
  exact (isFact_iff_closed (sInf S)).2 this

/--
Binary intersections of facts are facts.
-/
lemma inter_isFact_of_isFact [PhaseSpace M] {A B : Set M}
    (hA : isFact A) (hB : isFact B) : isFact (A ∩ B) := by
  have : isFact (sInf ({A,B} : Set (Set M))) := sInf_isFact (by
    intro X hX; rcases hX with rfl | rfl | _; simp [hA]; simp [hB])
  simpa [sInf_insert, sInf_singleton, inf_eq_inter] using this

/--
The idempotent elements within a given set X.
-/
def idempotentsIn [Monoid M] (X : Set M) : Set M := {m | IsIdempotentElem m ∧ m ∈ X}

/--
The interpretation of the multiplicative unit 1: the biorthogonal closure of {1}.
-/
def oneSet [PhaseSpace M] : Set M := ({1} : Set M)⫠⫠

@[simp] lemma oneSet_isFact [PhaseSpace M] : isFact (oneSet : Set M) := by
  simp [oneSet, isFact, triple_orth]

/--
The set I of idempotents that "belong to 1" in the phase semantics.
-/
def I [PhaseSpace M] : Set M := idempotentsIn (oneSet : Set M)

-- ## Interpretation of propositions

/--
The interpretation of a CLL proposition in a phase space, given a valuation of atoms to facts.
-/
def interp [PhaseSpace M] (v : Atom → Fact M) : Proposition Atom → Set M
  | .atom a       => v a
  | .atomDual a   => (v a)⫠
  | .one          => oneSet
  | .zero         => (∅ : Set M)⫠⫠
  | .top          => (Set.univ : Set M)
  | .bot          => oneSet⫠
  | .tensor X Y   => ((interp v X) * (interp v Y))⫠⫠
  | .parr    X Y   => (((interp v X)⫠) * ((interp v Y)⫠))⫠
  | .oplus  X Y   => ((interp v X) ∪ (interp v Y))⫠⫠
  | .with   X Y   => (interp v X) ∩ (interp v Y)
  | .bang   X     => ((interp v X) ∩ I)⫠⫠
  | .quest  X     => (((interp v X)⫠) ∩ I)⫠

@[inherit_doc] scoped notation:max "⟦" P "⟧" v:90 => interp v P

-- ## Main theorem

/--
The interpretation of any proposition in a phase space is always a fact.
-/
theorem interp_closed [PhaseSpace M] (v : Atom → Fact M) :
    isFact (⟦P⟧v) := by
  induction P <;> simp only [interp, isFact, triple_orth]
  · case atom x =>
    simpa [isFact] using (v x).property
  · case one => exact oneSet_isFact
  · case top => exact top_isFact
  · case _ X Y ih₁ ih₂ => exact inter_isFact_of_isFact ih₁ ih₂

/--
The interpretation of a proposition as a fact.
-/
def interp₁ [PhaseSpace M] (v : Atom → Fact M) (P : Proposition Atom) : Fact M :=
⟨⟦P⟧v, interp_closed v⟩

end PhaseSpace

end CLL
