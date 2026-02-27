module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import Cslib.Logics.LinearLogic.CLL.PhaseSemantics.Basic

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Pointwise.Set.Basic
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
    Sequent.IsMALL (Atom := Atom) Γ →
    Γ.Provable →
      ∀ (M : Type*) [PhaseSpace M] (v : Atom → Fact M),
        (interpSequent (Atom:=Atom) M v Γ).IsValid :=
by
  sorry

@[reducible] def CanonM (Atom : Type u) : Type u := Multiplicative (Sequent Atom)

def PrSet (Atom : Type u) (A : Proposition Atom) : Set (CanonM Atom) :=
  {m | Sequent.Provable (Atom := Atom) (A ::ₘ m.toAdd)}

theorem PrSet_top {Atom : Type u} : PrSet Atom (⊤ : Proposition Atom) =
(Set.univ : Set (CanonM Atom)) := by
  ext m
  constructor
  · intro a
    simp_all only [Set.mem_univ]
  · intro hm
    simp only [PrSet, Set.mem_setOf_eq]
    exact Sequent.Provable.fromProof (Proof.top (Γ := m.toAdd))

theorem PrSet_with {Atom : Type u} (A B : Proposition Atom) : PrSet Atom (A & B) =
  PrSet Atom A ∩ PrSet Atom B := by
  ext m
  constructor
  · intro hm
    simp only [PrSet, Set.mem_setOf_eq, Set.mem_inter_iff] at hm ⊢
    constructor
    · exact ⟨Proof.with_inversion₁ (a := A) (b := B) (Γ := m.toAdd) hm.toProof⟩
    · exact ⟨Proof.with_inversion₂ (a := A) (b := B) (Γ := m.toAdd) hm.toProof⟩
  · intro hm
    simp only [PrSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hm ⊢
    exact ⟨Proof.with (a := A) (b := B) (Γ := m.toAdd) hm.1.toProof hm.2.toProof⟩

def canonBot (Atom : Type u) : Set (CanonM Atom) :=
  {m | Sequent.Provable (Atom := Atom) m.toAdd}

theorem PrSet_bot {Atom : Type u} : PrSet Atom (⊥ : Proposition Atom) = canonBot Atom := by
  ext m
  unfold PrSet canonBot
  constructor
  · intro hm
    rcases hm with ⟨p⟩
    exact ⟨Proof.bot_inversion p⟩
  · intro hm
    rcases hm with ⟨p⟩
    exact ⟨Proof.bot p⟩

instance canonPhaseSpace (Atom : Type u) : PhaseSpace (CanonM Atom) := by
  let inst : CommMonoid (CanonM Atom) := inferInstance
  exact { bot := canonBot Atom, toCommMonoid := inst }

theorem PrSet_eq_orth {Atom : Type u} (A : Proposition Atom) :
PrSet Atom A = PhaseSpace.orthogonal (PrSet Atom (Proposition.dual A)) := by
  ext m
  constructor
  · intro hm
    unfold PhaseSpace.orthogonal PhaseSpace.imp
    intro n hn
    change (m * n) ∈ canonBot Atom
    simp only [canonBot, Set.mem_setOf_eq, toAdd_mul]
    refine Sequent.Provable.fromProof ?_
    exact Proof.rwConclusion (toAdd_mul m n).symm (hm.toProof.cut hn.toProof)
  · intro hm
    unfold PhaseSpace.orthogonal PhaseSpace.imp at hm
    let n : CanonM Atom := Multiplicative.ofAdd ({A} : Sequent Atom)
    have hn : n ∈ PrSet Atom (Proposition.dual A) := by
      simp only [PrSet, Set.mem_setOf_eq]
      simpa [n] using (Sequent.Provable.fromProof (Proof.ax' (a := A)))
    have hbot : m * n ∈ PhaseSpace.bot := hm n hn
    have hprov : Sequent.Provable (Atom := Atom) ((m * n).toAdd) := by
      aesop
    have hprov' : Sequent.Provable (Atom := Atom) (m.toAdd + ({A} : Sequent Atom)) := by
      aesop
    have hprov'' : Sequent.Provable (Atom := Atom) (({A} : Sequent Atom) + m.toAdd) := by
      grind only
    aesop

theorem PrSet_dual_eq_orth {Atom : Type u} (A : Proposition Atom) :
PrSet Atom (Proposition.dual A) = PhaseSpace.orthogonal (PrSet Atom A) := by
  simpa [Proposition.dual_involution] using (PrSet_eq_orth (Atom := Atom) (A := Proposition.dual A))

theorem PrSet_oplus {Atom : Type u} (A B : Proposition Atom) :
PrSet Atom (A ⊕ B) = PhaseSpace.orthogonal (PhaseSpace.orthogonal (PrSet Atom A ∪ PrSet Atom B)) :=
by
  rw [PrSet_eq_orth (Atom := Atom) (A := A ⊕ B)]
  have hdual : PrSet Atom (Proposition.dual (A ⊕ B)) =
      PhaseSpace.orthogonal (PrSet Atom A ∪ PrSet Atom B) := by
    simp only [Proposition.dual, orthogonal_def, Set.mem_union, Multiplicative.forall]
    rw [PrSet_with (Atom := Atom) (A := Proposition.dual A) (B := Proposition.dual B)]
    have hA : PrSet Atom (Proposition.dual A) = PhaseSpace.orthogonal (PrSet Atom A) := by
      simpa [Proposition.dual] using (PrSet_eq_orth (Atom := Atom) (A := Proposition.dual A))
    have hB : PrSet Atom (Proposition.dual B) = PhaseSpace.orthogonal (PrSet Atom B) := by
      simpa [Proposition.dual] using (PrSet_eq_orth (Atom := Atom) (A := Proposition.dual B))
    rw [hA, hB]
    ext m
    simp only [orthogonal, imp, Multiplicative.forall, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hmA, hmB⟩ a ha
      rcases ha with ha | ha <;> aesop
    · intro hm
      constructor <;> aesop
  rw [hdual]

theorem PrSet_parr {Atom : Type u} (A B : Proposition Atom) : PrSet Atom (A ⅋ B) =
PhaseSpace.orthogonal (PrSet Atom (Proposition.dual A) * PrSet Atom (Proposition.dual B)) := by
  ext m
  constructor
  · intro hm
    have pab : Sequent.Provable ((A ⅋ B) ::ₘ m.toAdd) := by
      exact hm
    change m ∈ PhaseSpace.orthogonal (PrSet Atom (A⫠) * PrSet Atom (B⫠))
    unfold PhaseSpace.orthogonal PhaseSpace.imp
    intro x hx
    rcases Set.mem_mul.mp hx with ⟨s, hs, t, ht, rfl⟩
    have ps : Sequent.Provable (A⫠ ::ₘ s.toAdd) := by simpa [PrSet] using hs
    have pt : Sequent.Provable (B⫠ ::ₘ t.toAdd) := by simpa [PrSet] using ht
    change Sequent.Provable ((m * (s * t)).toAdd)
    refine Sequent.Provable.fromProof ?_
    have hAB : ⇓(A ::ₘ B ::ₘ m.toAdd) := Proof.parr_inversion pab.toProof
    have hB : ⇓((B ::ₘ m.toAdd) + s.toAdd) := Proof.cut hAB ps.toProof
    have hB' : ⇓(B ::ₘ (m.toAdd + s.toAdd)) := by
      refine Proof.rwConclusion ?_ hB
      simp
    have hms : ⇓((m.toAdd + s.toAdd) + t.toAdd) := Proof.cut hB' pt.toProof
    refine Proof.rwConclusion ?_ hms
    simp [toAdd_mul, add_assoc]
  · intro hm
    unfold PhaseSpace.orthogonal PhaseSpace.imp at hm
    let s : CanonM Atom := Multiplicative.ofAdd ({A} : Sequent Atom)
    let t : CanonM Atom := Multiplicative.ofAdd ({B} : Sequent Atom)
    have hs : s ∈ PrSet Atom (A⫠) := by
      change Sequent.Provable (A⫠ ::ₘ s.toAdd)
      refine Sequent.Provable.fromProof ?_
      simpa [s] using (Proof.ax' (Atom := Atom) (a := A))
    have ht : t ∈ PrSet Atom (B⫠) := by
      change Sequent.Provable (B⫠ ::ₘ t.toAdd)
      refine Sequent.Provable.fromProof ?_
      simpa [t] using (Proof.ax' (Atom := Atom) (a := B))
    have hst : s * t ∈ (PrSet Atom (A⫠) * PrSet Atom (B⫠)) := Set.mul_mem_mul hs ht
    have hbot : m * (s * t) ∈ bot := hm (s * t) hst
    have hprov : Sequent.Provable ((m * (s * t)).toAdd) := by
      simpa [canonBot] using hbot
    have habm : ⇓(A ::ₘ B ::ₘ m.toAdd) := by
      refine (hprov.toProof).rwConclusion ?_
      simp [s, t, toAdd_mul, add_comm, Multiset.singleton_add]
    have : Sequent.Provable ((A ⅋ B) ::ₘ m.toAdd) :=
      Sequent.Provable.fromProof (Proof.parr habm)
    simpa [PrSet] using this

theorem PrSet_tensor {Atom : Type u} (A B : Proposition Atom) : PrSet Atom (A ⊗ B) =
PhaseSpace.orthogonal (PhaseSpace.orthogonal (PrSet Atom A * PrSet Atom B)) := by
  rw [PrSet_eq_orth (Atom := Atom) (A := A ⊗ B)]
  congr 1
  simpa [Proposition.dual] using
      (PrSet_parr (Atom := Atom) (A := Proposition.dual A) (B := Proposition.dual B))

def canonVal {Atom : Type u} (a : Atom) : Fact (CanonM Atom) :=
  PhaseSpace.dualFact (PrSet Atom (Proposition.atomDual a))

noncomputable def foldPar {Atom : Type u} (Γ : Sequent Atom) : Proposition Atom :=
  (Multiset.toList Γ).foldr (· ⅋ ·) ⊥

theorem foldPar_isMALL {Atom : Type u} (Γ : Sequent Atom)
    (h : Sequent.IsMALL (Atom := Atom) Γ) :
    Proposition.IsMALL (Atom := Atom) (foldPar (Atom := Atom) Γ) := by
  have foldr_parr_isMALL :
      ∀ l : List (Proposition Atom),
        (∀ A ∈ l, (A : Proposition Atom).IsMALL) →
          Proposition.IsMALL (Atom := Atom)
            (List.foldr (fun A B : Proposition Atom => A ⅋ B) (⊥ : Proposition Atom) l) := by
    intro l hl
    induction l with
    | nil =>
        simp [Proposition.IsMALL]
    | cons a l ih =>
        have ha : (a : Proposition Atom).IsMALL := hl a (by simp)
        have hl' : ∀ A ∈ l, (A : Proposition Atom).IsMALL := by
          intro A hA
          exact hl A (by simp [hA])
        have hacc :=
          ih hl'
        simpa [Proposition.IsMALL, ha] using And.intro ha hacc
  have hlist : ∀ A ∈ Multiset.toList Γ, (A : Proposition Atom).IsMALL := by
    intro A hA
    exact h A (by
      simpa using (Multiset.mem_toList.1 hA))
  simpa [foldPar] using foldr_parr_isMALL (Multiset.toList Γ) hlist

theorem interpProp_canon_carrier {Atom : Type u} (A : Proposition Atom)
    (hA : Proposition.IsMALL (Atom := Atom) A) :
    ((interpProp (Atom:=Atom) (M:=CanonM Atom) (canonVal (Atom:=Atom)) A : Fact (CanonM Atom)) :
        Set (CanonM Atom)) =
      PrSet Atom A := by
  induction A with
  | atom a =>
      simp only [interpProp, canonVal, dualFact, mk_dual_coe]
      rw [PrSet_eq_orth (Atom := Atom) (A := Proposition.atom a)]
      simp [Proposition.dual, -PhaseSpace.orthogonal_def]
  | atomDual a =>
      simp only [interpProp, canonVal, dualFact, coe_neg, mk_dual_coe]
      conv_rhs =>
        rw [PrSet_eq_orth (Atom := Atom) (A := Proposition.atomDual a)]
      simp only [Proposition.dual]
      rw [PrSet_eq_orth (Atom := Atom) (A := Proposition.atom a)]
      simp [Proposition.dual, -PhaseSpace.orthogonal_def]
  | one =>
      simp only [interpProp, coe_one]
      rw [PrSet_eq_orth (Atom := Atom) (A := Proposition.one)]
      simp only [Proposition.dual]
      have hb : PrSet Atom (Proposition.bot : Proposition Atom) = canonBot Atom := by
        simpa using (PrSet_bot (Atom := Atom))
      rw [hb]
      rfl
  | zero =>
      simp only [interpProp, coe_zero]
      rw [PrSet_eq_orth (Atom := Atom) (A := Proposition.zero)]
      simp only [Proposition.dual]
      have ht : PrSet Atom (Proposition.top : Proposition Atom) = (Set.univ : Set (CanonM Atom)) :=
      by simpa using (PrSet_top (Atom := Atom))
      rw [ht]
  | top =>
      simpa [PhaseSpace.interpProp] using (PrSet_top (Atom := Atom)).symm
  | bot =>
      simpa [PhaseSpace.interpProp] using (PrSet_bot (Atom := Atom)).symm
  | tensor A B ihA ihB =>
      have hA' : Proposition.IsMALL (Atom := Atom) A := hA.1
      have hB' : Proposition.IsMALL (Atom := Atom) B := hA.2
      simp [PhaseSpace.interpProp, ihA hA', ihB hB', Fact.tensor, PhaseSpace.dualFact, PrSet_tensor,
        -PhaseSpace.orthogonal_def]
  | parr A B ihA ihB =>
      have hA' : Proposition.IsMALL (Atom := Atom) A := hA.1
      have hB' : Proposition.IsMALL (Atom := Atom) B := hA.2
      simp [PhaseSpace.interpProp, ihA hA', ihB hB', Fact.parr, PhaseSpace.dualFact, PrSet_parr,
        PrSet_dual_eq_orth, -PhaseSpace.orthogonal_def]
  | oplus A B ihA ihB =>
      have hA' : Proposition.IsMALL (Atom := Atom) A := hA.1
      have hB' : Proposition.IsMALL (Atom := Atom) B := hA.2
      simp [PhaseSpace.interpProp, ihA hA', ihB hB', Fact.oplus, PhaseSpace.dualFact, PrSet_oplus,
        -PhaseSpace.orthogonal_def]
  | «with» A B ihA ihB =>
      have hA' : Proposition.IsMALL (Atom := Atom) A := hA.1
      have hB' : Proposition.IsMALL (Atom := Atom) B := hA.2
      simp [PhaseSpace.interpProp, ihA hA', ihB hB', Fact.withh, PrSet_with]
  | bang A ih =>
      exact False.elim hA
  | quest A ih =>
      exact False.elim hA

theorem interpProp_list_foldr_parr {Atom : Type u} {M : Type*} [PhaseSpace M]
(v : Atom → Fact M) (l : List (Proposition Atom)) :
interpProp v (List.foldr (fun A B : Proposition Atom => A ⅋ B)
(⊥ : Proposition Atom) l) = List.foldr (fun (A : Proposition Atom)
(acc : Fact M) => (interpProp v A : Fact M) ⅋ acc) (⊥ : Fact M) l := by
  induction l with
  | nil =>
      simp [List.foldr, PhaseSpace.interpProp]
  | cons a l ih =>
      simp [List.foldr, PhaseSpace.interpProp, ih]

theorem interpSequent_eq_interpProp_foldPar {Atom : Type u} (M : Type*) [PhaseSpace M]
(v : Atom → Fact M) (Γ : Sequent Atom) :
interpSequent (Atom:=Atom) M v Γ = interpProp v (foldPar (Atom:=Atom) Γ) := by
  simp only [interpSequent, foldPar]
  rw [interpProp_list_foldr_parr (Atom := Atom) (M := M) v (Multiset.toList Γ)]
  have hfold :
      ∀ l : List (Proposition Atom),
        List.foldr
            (fun (A : Proposition Atom) (acc : Fact M) => (interpProp v A : Fact M) ⅋ acc)
            (⊥ : Fact M) l =
          List.foldr (fun x y : Fact M => x ⅋ y) (⊥ : Fact M)
            (l.map fun A => (interpProp v A : Fact M)) := by
    intro l
    induction l with
    | nil =>
        simp
    | cons a l ih =>
        simp [ih]
  rw [hfold (l := Multiset.toList Γ)]
  have hΓ : ((Multiset.toList Γ) : Multiset (Proposition Atom)) = Γ := by
    simp
  calc
    (Γ.map (fun A => (interpProp v A : Fact M))).fold (fun x y : Fact M => x ⅋ y) (⊥ : Fact M)
        = (((Multiset.toList Γ) : Multiset (Proposition Atom)).map (fun A =>
        (interpProp v A : Fact M))).fold
            (fun x y : Fact M => x ⅋ y) (⊥ : Fact M) := by
            simp [hΓ]
    _ = (((Multiset.toList Γ).map (fun A => (interpProp v A : Fact M)) : List (Fact M)) :
            Multiset (Fact M)).fold (fun x y : Fact M => x ⅋ y) (⊥ : Fact M) := by
          simpa using
            congrArg
              (fun s : Multiset (Fact M) =>
                s.fold (fun x y : Fact M => x ⅋ y) (⊥ : Fact M))
              (Multiset.map_coe
                (f := fun A : Proposition Atom => (interpProp v A : Fact M))
                (l := Multiset.toList Γ))
    _ = List.foldr (fun x y : Fact M => x ⅋ y) (⊥ : Fact M)
            ((Multiset.toList Γ).map (fun A => (interpProp v A : Fact M))) := by
          simp

theorem provable_of_list_foldr_parr {Atom : Type u} (l : List (Proposition Atom)) (Δ : Sequent Atom)
: Sequent.Provable (Atom:=Atom) ((List.foldr (fun A B : Proposition Atom => A ⅋ B)
(⊥ : Proposition Atom) l) ::ₘ Δ) → Sequent.Provable (Atom:=Atom) ((l : Sequent Atom) + Δ) := by
  induction l generalizing Δ with
  | nil =>
      intro h
      rcases h with ⟨p⟩
      have pΔ : ⇓Δ := Proof.bot_inversion p
      refine (Sequent.Provable.fromProof ?_)
      simpa using pΔ
  | cons a l ih =>
      intro h
      rcases h with ⟨p⟩
      have p' :
      ⇓(a ::ₘ (List.foldr (fun A B : Proposition Atom => A ⅋ B) (⊥ : Proposition Atom) l) ::ₘ Δ) :=
        Proof.parr_inversion p
      have p'' :
      ⇓((List.foldr (fun A B : Proposition Atom => A ⅋ B) (⊥ : Proposition Atom) l) ::ₘ a ::ₘ Δ) :=
        Proof.rwConclusion (Multiset.cons_swap a (List.foldr (fun A B : Proposition Atom => A ⅋ B)
        (⊥ : Proposition Atom) l) Δ) p'
      have hprov : Sequent.Provable (Atom:=Atom)
          ((l : Sequent Atom) + (a ::ₘ Δ)) :=
        ih (Δ := a ::ₘ Δ) ⟨p''⟩
      rcases hprov with ⟨q⟩
      have hEq : ((l : Sequent Atom) + (a ::ₘ Δ)) = ((a :: l : Sequent Atom) + Δ) := by
        calc
          (l : Sequent Atom) + (a ::ₘ Δ)
              = a ::ₘ ((l : Sequent Atom) + Δ) := by
                    simp
          _ = (a ::ₘ (l : Sequent Atom)) + Δ := by
                    simpa using (Multiset.cons_add a (l : Sequent Atom) Δ).symm
          _ = (a :: l : Sequent Atom) + Δ := by
                    simp
      exact ⟨Proof.rwConclusion hEq q⟩

theorem provable_of_foldPar {Atom : Type u} (Γ : Sequent Atom) : ({foldPar (Atom:=Atom) Γ} :
Sequent Atom).Provable → Γ.Provable := by
  intro h
  have h' :
      Sequent.Provable (Atom:=Atom)
        ((List.foldr (fun A B : Proposition Atom => A ⅋ B)
        (⊥ : Proposition Atom) (Multiset.toList Γ)) ::ₘ
            (0 : Sequent Atom)) := by
    simpa [foldPar] using h
  have h'' :
      Sequent.Provable (Atom:=Atom) (((Multiset.toList Γ) : Sequent Atom) + (0 : Sequent Atom)) :=
    provable_of_list_foldr_parr (Atom:=Atom) (l := Multiset.toList Γ) (Δ := (0 : Sequent Atom)) h'
  have h''' : Sequent.Provable (Atom:=Atom) ((Multiset.toList Γ) : Sequent Atom) := by
    simpa using h''
  simpa [Multiset.coe_toList Γ] using h'''

theorem completeness {Atom : Type u} (Γ : Sequent Atom)
    (hMALL : Sequent.IsMALL (Atom := Atom) Γ) :
    (∀ (M : Type u) [PhaseSpace M] (v : Atom → Fact M),
        (interpSequent (Atom:=Atom) M v Γ).IsValid) → Γ.Provable := by
  intro h
  have hv := h (M := CanonM Atom) (v := canonVal (Atom := Atom))
  have hv1 : (1 : CanonM Atom) ∈ (interpSequent (Atom := Atom) (CanonM Atom)
  (canonVal (Atom := Atom)) Γ : Set (CanonM Atom)) := by
    simpa [PhaseSpace.Fact.IsValid] using hv
  have hv2 : (1 : CanonM Atom) ∈ (interpProp (Atom := Atom) (M := CanonM Atom)
  (canonVal (Atom := Atom)) (foldPar (Atom := Atom) Γ) : Set (CanonM Atom)) := by
    simpa
    [interpSequent_eq_interpProp_foldPar] using hv1
  have hv3 : (1 : CanonM Atom) ∈ PrSet Atom (foldPar (Atom := Atom) Γ) := by
    have hFold :
        Proposition.IsMALL (Atom := Atom) (foldPar (Atom := Atom) Γ) :=
      foldPar_isMALL (Atom := Atom) Γ hMALL
    simpa [interpProp_canon_carrier (Atom := Atom) (A := foldPar (Atom := Atom) Γ) hFold] using hv2
  have hprov : ({foldPar (Atom := Atom) Γ} : Sequent Atom).Provable := by
    simp_all only [SetLike.mem_coe]
    exact hv3
  exact provable_of_foldPar (Atom := Atom) Γ hprov

end CLL
end Cslib
