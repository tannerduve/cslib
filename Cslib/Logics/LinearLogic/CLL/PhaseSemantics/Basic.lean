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

## TODO
- Soundness
- Completeness

## References

* [J.-Y. Girard, *Linear Logic: its syntax and semantics*][Girard1995]
-/

universe u v

namespace CLL

open Proposition
open scoped Pointwise
open Set

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
lemma orthogonal_extensive [PhaseSpace M] (X : Set M) : X ⊆ X⫠⫠ := by
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
  · apply orthogonal_extensive (X := X⫠)

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

lemma univ_closed [PhaseSpace M] :
    (Set.univ : Set M) = biorthogonalClosure univ := by
  symm
  simpa [top_eq_univ]
    using ClosureOperator.closure_top (CLL.PhaseSpace.biorthogonalClosure (M:=M))

/--
A fact is a subset of a phase space that is equal to its biorthogonal
-/
def isFact [PhaseSpace M] (X : Set M) : Prop := X = X⫠⫠

/--
The type of facts in a phase space
-/
abbrev Fact (M : Type u) [PhaseSpace M] := { X : Set M // isFact X }

instance [PhaseSpace M] : Coe (Fact M) (Set M) := ⟨Subtype.val⟩
@[simp] lemma coe_mk [PhaseSpace M] {X : Set M} {h : isFact (M := M) X} :
    ((⟨X, h⟩ : Fact M) : Set M) = X := rfl
@[simp] lemma closed [PhaseSpace M] (F : Fact M) : isFact (M := M) (F : Set M) := F.property

/--
A set is a fact if and only if it is of the form `Y⫠` for some `Y`.
-/
lemma fact_iff_exists_orth [PhaseSpace M] (X : Set M) :
    isFact X ↔ ∃ Y : Set M, X = Y⫠ := by
  constructor
  · intro hX
    refine ⟨X⫠, ?_⟩
    exact hX
  · rintro ⟨Y, rfl⟩
    simp [isFact, triple_orth (X := Y)]

/--
If Y is a fact, then X ⊸ Y is a fact
-/
lemma imp_isFact_of_fact
    [PhaseSpace M]
    (X Y : Set M) (hY : isFact Y) :
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

def Fact.imp [PhaseSpace M] (X : Set M) (Y : Fact M) : Fact M :=
  ⟨ X ⊸ Y, imp_isFact_of_fact X Y Y.property ⟩

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

lemma inter_closed_of_closed [PhaseSpace M] {A B : Set M}
    (hA : isFact A) (hB : isFact B) :
    isFact (A ∩ B) := by
  have h₁ : A ∩ B ⊆ (A ∩ B)⫠⫠ := orthogonal_extensive _
  have h₂A : (A ∩ B)⫠⫠ ⊆ A := by
    have hmono : (A ∩ B)⫠⫠ ⊆ A⫠⫠ := by
      change biorthogonalClosure (A ∩ B) ⊆ biorthogonalClosure A
      exact PhaseSpace.biorthogonalClosure.monotone' (by
        intro x hx; exact hx.1)
    rw [← hA] at hmono; exact hmono;
  have h₂B : (A ∩ B)⫠⫠ ⊆ B := by
    have hmono : (A ∩ B)⫠⫠ ⊆ B⫠⫠ := by
      change biorthogonalClosure (A ∩ B) ⊆ biorthogonalClosure B
      exact PhaseSpace.biorthogonalClosure.monotone' (by
        intro x hx; exact hx.2)
    rw [← hB] at hmono; exact hmono
  apply le_antisymm h₁
  intro x hx; exact ⟨h₂A hx, h₂B hx⟩

lemma isFact_iff_closed [PhaseSpace M] (X : Set M) :
  isFact X ↔ biorthogonalClosure.IsClosed X := by
  constructor <;> (intro; simp only [isFact, biorthogonalClosure]; symm; assumption)

/--
If each X in S is a fact, then the intersection of all X in S is a fact
-/
lemma sInf_isFact [PhaseSpace M] {S : Set (Set M)}
    (H : ∀ X ∈ S, isFact X) :
    isFact (sInf S) := by
  have H' : ∀ X ∈ S, biorthogonalClosure.IsClosed X :=
    fun X hX => (isFact_iff_closed (X := X)).1 (H X hX)
  have : biorthogonalClosure.IsClosed (sInf S) :=
    ClosureOperator.sInf_isClosed (c := biorthogonalClosure) (S := S) H'
  exact (isFact_iff_closed (X := sInf S)).2 this

/--
If A and B are facts, then A ∩ B is a fact
-/
lemma inter_isFact_of_isFact [PhaseSpace M] {A B : Set M}
    (hA : isFact A) (hB : isFact B) :
    isFact (A ∩ B) := by
  have : isFact (sInf ({A,B} : Set (Set M))) := sInf_isFact (by
    intro X hX; rcases hX with rfl | rfl | _; simp [hA]; simp [hB])
  simpa [sInf_insert, sInf_singleton, inf_eq_inter] using this

end PhaseSpace

end CLL
