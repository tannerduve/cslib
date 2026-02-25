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

/-- Semantic interpretation of a sequent as the par-fold of its members. -/
def interpSequent
    (M : Type*) [PhaseSpace M]
    (v : Atom → Fact M)
    (Γ : Sequent Atom) : Fact M :=
  (Γ.map (fun A => (interpProp v A : Fact M))).fold (· ⅋ ·) ⊥

/-- Provable sequents are valid in every phase space under every valuation. -/
theorem soundness
    (Γ : Sequent Atom) :
    Γ.Provable →
      ∀ (M : Type*) [PhaseSpace M] (v : Atom → Fact M),
        (interpSequent (Atom:=Atom) M v Γ).IsValid :=
by
  sorry

/-- If a sequent is valid in every phase space under every valuation,
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
