module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import Cslib.Logics.LinearLogic.CLL.PhaseSemantics.Basic

@[expose] public section

namespace Cslib
namespace CLL

open scoped Pointwise
open PhaseSpace
open PhaseSpace.Fact

universe u

variable {Atom : Type u}

namespace PhaseSemantics

/-- `!` and `ʔ` are dual to each other. -/
lemma quest_neg
    {M : Type*} [PhaseSpace M] (G : Fact M) :
    Fact.quest (P := M) (Gᗮ) = (Fact.bang (P := M) G)ᗮ := by
  apply SetLike.coe_injective
  -- `Gᗮ⫠ = G` for facts, and `X⫠⫠⫠ = X⫠`.
  -- Keep the proof explicit to avoid `simp` loops.
  simp only [Fact.quest, Fact.bang, dualFact_coe, coe_neg]
  -- use that `G` is a fact: `G⫠⫠ = G`
  rw [(Fact.eq (G := G)).symm]
  -- and finish with `X⫠⫠⫠ = X⫠`
  simpa using (triple_orth (X := (G : Set M) ∩ I)).symm

/-- `!` and `ʔ` are dual to each other (the other direction). -/
lemma bang_neg
    {M : Type*} [PhaseSpace M] (G : Fact M) :
    Fact.bang (P := M) (Gᗮ) = (Fact.quest (P := M) G)ᗮ := by
  apply SetLike.coe_injective
  simp only [Fact.quest, Fact.bang, dualFact_coe, coe_neg]
  -- both sides reduce to the same set
  rfl

/-- `interpProp` commutes with propositional duality. -/
@[simp] lemma interpProp_dual
    {M : Type*} [PhaseSpace M] (v : Atom → Fact M) (A : Proposition Atom) :
    interpProp v (A⫠) = (interpProp v A)ᗮ := by
  induction A <;>
    simp [Proposition.dual, PhaseSpace.interpProp, *, neg_tensor, neg_par, neg_plus, neg_with,
      PhaseSemantics.quest_neg, PhaseSemantics.bang_neg]

/-- Validity of a linear implication is just inclusion. -/
lemma le_iff_linImpl_valid
    {M : Type*} [PhaseSpace M] {G H : Fact M} :
    G ≤ H ↔ (G ⊸ H).IsValid := by
  constructor
  · intro h
    have : imp (M := M) (G : Set M) (H : Set M) (1 : M) := by
      intro x hx
      aesop
    exact (linImpl_iff_implies (G := G) (H := H) (p := (1 : M))).2 this
  · intro h x hx
    have : imp (M := M) (G : Set M) (H : Set M) (1 : M) :=
      (linImpl_iff_implies (G := G) (H := H) (p := (1 : M))).1 h
    simpa [PhaseSpace.imp, one_mul] using this x hx

end PhaseSemantics

/-- Semantic interpretation of a sequent as the par-fold of its members. -/
def interpSequent
    (M : Type*) [PhaseSpace M]
    (v : Atom → Fact M)
    (Γ : Sequent Atom) : Fact M :=
  (Γ.map (fun A => (interpProp v A : Fact M))).fold (· ⅋ ·) ⊥

namespace PhaseSemantics

@[simp] lemma interpSequent_zero
    (M : Type*) [PhaseSpace M] (v : Atom → Fact M) :
    interpSequent (Atom := Atom) M v (0 : Sequent Atom) = (⊥ : Fact M) := by
  rfl

@[simp] lemma interpSequent_cons
    (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A : Proposition Atom) (Γ : Sequent Atom) :
    interpSequent (Atom := Atom) M v (A ::ₘ Γ) =
      (interpProp v A : Fact M) ⅋ interpSequent (Atom := Atom) M v Γ := by
  simp [interpSequent, Multiset.map_cons, Multiset.fold_cons_left]

@[simp] lemma interpSequent_add
    (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (Γ Δ : Sequent Atom) :
    interpSequent (Atom := Atom) M v (Γ + Δ) =
      interpSequent (Atom := Atom) M v Γ ⅋ interpSequent (Atom := Atom) M v Δ := by
  refine Multiset.induction_on Δ ?h0 ?hs
  · simp [interpSequent_zero, par_bot]
  · intro A Δ ih
    have : Γ + (A ::ₘ Δ) = A ::ₘ (Γ + Δ) := by
      simp
    rw [this, interpSequent_cons, ih, interpSequent_cons]
    have par_comm' (X Y : Fact M) :
        PhaseSpace.Fact.parr X Y = PhaseSpace.Fact.parr Y X := by
      simpa using (PhaseSpace.Fact.par_comm X Y)
    have par_assoc' (X Y Z : Fact M) :
        PhaseSpace.Fact.parr (PhaseSpace.Fact.parr X Y) Z =
          PhaseSpace.Fact.parr X (PhaseSpace.Fact.parr Y Z) := by
      simp
    simpa using (show
      PhaseSpace.Fact.parr (interpProp v A : Fact M)
          (PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Γ) (interpSequent (Atom := Atom) M v Δ))
        =
      PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Γ)
          (PhaseSpace.Fact.parr (interpProp v A : Fact M) (interpSequent (Atom := Atom) M v Δ)) from
      calc
        PhaseSpace.Fact.parr (interpProp v A : Fact M)
            (PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Γ) (interpSequent (Atom := Atom) M v Δ))
            =
          PhaseSpace.Fact.parr
            (PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Γ) (interpSequent (Atom := Atom) M v Δ))
            (interpProp v A : Fact M) := by
              simpa using par_comm' (interpProp v A : Fact M)
                (PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Γ) (interpSequent (Atom := Atom) M v Δ))
        _ =
          PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Γ)
            (PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Δ) (interpProp v A : Fact M)) := by
              simp
        _ =
          PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Γ)
            (PhaseSpace.Fact.parr (interpProp v A : Fact M) (interpSequent (Atom := Atom) M v Δ)) := by
              simpa using congrArg
                (fun T => PhaseSpace.Fact.parr (interpSequent (Atom := Atom) M v Γ) T)
                (par_comm' (interpSequent (Atom := Atom) M v Δ) (interpProp v A : Fact M))
      )
            

end PhaseSemantics

/-- Provable sequents are valid in every phase space under every valuation. -/
theorem soundness
    (Γ : Sequent Atom) :
    Γ.Provable →
      ∀ (M : Type*) [PhaseSpace M] (v : Atom → Fact M),
        (interpSequent (Atom:=Atom) M v Γ).IsValid :=
by
  sorry

/-- Completeness: if a sequent is valid in every phase space under every valuation,
then it is provable. -/
theorem completeness
    (Γ : Sequent Atom) :
    (∀ (M : Type*) [PhaseSpace M] (v : Atom → Fact M),
        (interpSequent (Atom:=Atom) M v Γ).IsValid) →
      Γ.Provable :=
by
  sorry

end CLL
end Cslib
