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
theorem IsValid_monotone {M : Type*} [PhaseSpace M]
{G H : Fact M} : G ≤ H → G.IsValid → H.IsValid := by
  intro hGH hG
  simpa [Fact.IsValid] using hGH (by simpa [Fact.IsValid] using hG)

theorem dualFact_coe (M : Type*) [PhaseSpace M] (S : Set M) :
((PhaseSpace.dualFact (P:=M) S : Fact M) : Set M) = S⫠ := by
  simp [PhaseSpace.dualFact]

theorem interpProp_atomDual (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (a : Atom) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.atomDual a) : Fact M) = ((v a)ᗮ : Fact M) := by
  simp [PhaseSpace.interpProp]

theorem interpProp_bang (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A : Proposition Atom) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.bang A) : Fact M) =
(PhaseSpace.Fact.bang (interpProp (Atom:=Atom) (M:=M) v A)) := by
  simp [interpProp]

theorem interpProp_bot (M : Type*) [PhaseSpace M] (v : Atom → Fact M) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.bot : Proposition Atom) : Fact M) =
(⊥ : Fact M) := by
  simp [PhaseSpace.interpProp, interpProp]

theorem interpProp_one (M : Type*) [PhaseSpace M] (v : Atom → Fact M) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.one : Proposition Atom) : Fact M) =
(1 : Fact M) := by
  simp [interpProp]

theorem interpProp_oplus (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A B : Proposition Atom) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.oplus A B) : Fact M) =
(PhaseSpace.Fact.oplus (interpProp (Atom:=Atom) (M:=M) v A)
(interpProp (Atom:=Atom) (M:=M) v B)) := by
  simp [PhaseSpace.interpProp]

theorem interpProp_parr (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A B : Proposition Atom) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.parr A B) : Fact M) = (interpProp (Atom:=Atom)
(M:=M) v A ⅋ interpProp (Atom:=Atom) (M:=M) v B) := by
  simp [PhaseSpace.interpProp]

theorem interpProp_quest (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A : Proposition Atom) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.quest A) : Fact M) = (PhaseSpace.Fact.quest
(interpProp (Atom:=Atom) (M:=M) v A)) := by
  simp [PhaseSpace.interpProp, PhaseSpace.Fact.quest]


theorem interpProp_tensor (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A B : Proposition Atom) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.tensor A B) : Fact M) = (interpProp (Atom:=Atom)
(M:=M) v A ⊗ interpProp (Atom:=Atom) (M:=M) v B) := by
  simp [interpProp]

theorem interpProp_top (M : Type*) [PhaseSpace M] (v : Atom → Fact M) : (interpProp (Atom:=Atom)
(M:=M) v (Proposition.top : Proposition Atom) : Fact M) = (⊤ : Fact M) := by
  simp [PhaseSpace.interpProp]

theorem interpProp_with (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A B : Proposition Atom) :
(interpProp (Atom:=Atom) (M:=M) v (Proposition.with A B) : Fact M) = (PhaseSpace.Fact.withh
(interpProp (Atom:=Atom) (M:=M) v A) (interpProp (Atom:=Atom) (M:=M) v B)) := by
  simp [interpProp, PhaseSpace.Fact.withh]

theorem interpSequent_nil (M : Type*) [PhaseSpace M] (v : Atom → Fact M) : interpSequent
(Atom:=Atom) M v (0 : Sequent Atom) = (⊥ : Fact M) := by
  -- attempt to unfold and simp
  simp [interpSequent]

theorem interpSequent_add (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (Γ Δ : Sequent Atom) :
interpSequent (Atom:=Atom) M v (Γ + Δ) = interpSequent (Atom:=Atom) M v Γ ⅋ interpSequent
(Atom:=Atom) M v Δ := by
  simp only [interpSequent]
  rw [Multiset.map_add]
  rw [← Fact.bot_par (G := (⊥ : Fact M))]
  simpa using
    (Multiset.fold_add
      (op := fun (x y : Fact M) => x ⅋ y)
      (b₁ := (⊥ : Fact M)) (b₂ := (⊥ : Fact M))
      (s₁ := Γ.map (fun A => (interpProp v A : Fact M)))
      (s₂ := Δ.map (fun A => (interpProp v A : Fact M))))

theorem interpSequent_cons (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A : Proposition Atom)
(Γ : Sequent Atom) : interpSequent (Atom:=Atom) M v (A ::ₘ Γ) =
(interpProp v A : Fact M) ⅋ interpSequent (Atom:=Atom) M v Γ := by
  simp [interpSequent]

theorem one_valid (M : Type*) [PhaseSpace M] : (1 : Fact M).IsValid := by
  simp [Fact.IsValid]

theorem quest_contract_le {M : Type*} [PhaseSpace M] (G : Fact M) : (PhaseSpace.Fact.parr
(PhaseSpace.Fact.quest G) (PhaseSpace.Fact.quest G) : Fact M) ≤ PhaseSpace.Fact.quest G := by
  intro m hm
  change m ∈ ((PhaseSpace.Fact.parr (PhaseSpace.Fact.quest G) (PhaseSpace.Fact.quest G) : Fact M) :
  Set M) at hm
  change m ∈ ((PhaseSpace.Fact.quest G : Fact M) : Set M)
  simp only [parr, quest, orthogonal_def, SetLike.mem_coe, PhaseSpace.dualFact_coe,
    Set.mem_inter_iff, Set.mem_setOf_eq, and_imp] at hm ⊢
  intro x hxG hxI
  have hxidem : IsIdempotentElem x := hxI.1
  have hxS : x ∈ ({m : M | ∀ x_1 ∈ G, m * x_1 ∈ bot} ∩ I) := by
    exact ⟨hxG, hxI⟩
  have hxQ : x ∈
      {m : M | ∀ (x : M),
      (∀ (x_1 : M), (∀ x ∈ G, x_1 * x ∈ bot) → x_1 ∈ I → x * x_1 ∈ bot) → m * x ∈ bot} := by
    have : x ∈ ({m : M | ∀ x_1 ∈ G, m * x_1 ∈ bot} ∩ I)⫠⫠ :=
      (PhaseSpace.orth_extensive (X := ({m : M | ∀ x_1 ∈ G, m * x_1 ∈ bot} ∩ I)) hxS)
    simpa [PhaseSpace.orthogonal_def] using this
  have hmbot : m * (x * x) ∈ bot := by
    apply hm (x * x)
    refine Set.mem_mul.mpr ?_
    exact ⟨x, hxQ, x, hxQ, rfl⟩
  simpa [hxidem.eq] using hmbot

theorem quest_le {M : Type*} [PhaseSpace M] (G : Fact M) : G ≤ PhaseSpace.Fact.quest G := by
  intro x hx
  change x ∈ ((PhaseSpace.Fact.quest G : Fact M) : Set M)
  simp only [quest, orthogonal_def, SetLike.mem_coe, PhaseSpace.dualFact_coe, Set.mem_inter_iff,
    Set.mem_setOf_eq, and_imp]
  intro y hy hyI
  have : y * x ∈ PhaseSpace.bot := hy x hx
  simpa [mul_comm] using this

theorem bot_le_quest {M : Type*} [PhaseSpace M] (G : Fact M) :
    (⊥ : Fact M) ≤ PhaseSpace.Fact.quest G := by
  intro m hm
  change m ∈ (((((G : Fact M) : Set M)⫠) ∩ PhaseSpace.I (P := M))⫠ : Set M)
  · change m ∈ (PhaseSpace.bot : Set M) at hm
    simp only [PhaseSpace.orthogonal_def, Set.mem_setOf_eq] at *
    intro x hx
    rcases hx with ⟨-, hxI⟩
    have hx1 : x ∈ (1 : Fact M) := hxI.2
    have hxm : x * m ∈ PhaseSpace.bot := (PhaseSpace.mem_one (P := M) (p := x)).1 hx1 m hm
    simpa [mul_comm] using hxm

theorem bang_valid_of_allQuest {M : Type*} [PhaseSpace M] {v : Atom → Fact M} {a : Proposition Atom} {Γ : Sequent Atom} : Γ.allQuest → (interpProp (Atom:=Atom) (M:=M) v a ⅋ interpSequent (Atom:=Atom) M v Γ).IsValid → ((PhaseSpace.Fact.bang (interpProp (Atom:=Atom) (M:=M) v a)) ⅋ interpSequent (Atom:=Atom) M v Γ).IsValid := by
  -- Soundness of **promotion** in a `?`-context.
  --
  -- Goal after unfolding `Fact.IsValid` is membership `1 ∈ !⟦a⟧ ⅋ ⟦Γ⟧` assuming `1 ∈ ⟦a⟧ ⅋ ⟦Γ⟧` and `Γ.allQuest`.
  --
  -- Key idea: `Γ.allQuest` means every element of `Γ` is a `Proposition.quest _`; hence every factor in `interpSequent M v Γ` is of the form `ʔG`, so `interpSequent M v Γ` is a `⅋`-combination of `ʔ`-facts. Use the semantic structural laws already available:
  -- - dereliction `quest_le` (to move from a fact into its `ʔ`),
  -- - weakening `bot_le_quest` (to introduce extra `ʔ` factors if needed),
  -- - contraction `quest_contract_le` (to eliminate duplicates under `⅋`).
  -- Together these show that in a `?`-context the sequent interpretation is **insensitive** to replacing `⟦a⟧` by `!⟦a⟧`.
  --
  -- Suggested formal path:
  -- 1. Unfold `PhaseSpace.Fact.bang` and coe via `dualFact_coe`, so the goal becomes a statement about orthogonals (`⫠`) and the idempotent set `I`.
  -- 2. Use `Γ.allQuest` to obtain (by induction on the multiset using `Multiset.induction_on`) that `interpSequent M v Γ ≤ PhaseSpace.Fact.quest (interpSequent M v Γ)` and also a contraction property for the `⅋`-fold. (You can prove intermediate `≤` statements inside the proof using `quest_le`, `bot_le_quest`, `quest_contract_le`, and `Fact.par_le_par` from the library.)
  -- 3. Convert the assumption validity into a monotone form using `IsValid_monotone` and the `≤` results built in step 2.
  -- 4. Finish with `aesop`/`grind` after unfolding orthogonality (`PhaseSpace.orthogonal_def`) and basic par simp lemmas (`Fact.par_assoc`, `Fact.par_comm`, `Fact.par_bot`, `Fact.bot_par`).
  --
  -- If this is still hard, try proving the contrapositive using orthogonality: show `1 ∈ (!G ⅋ H)` by showing `1 ∈ ((G ⅋ H))` and `(!G ⅋ H) = (G ⅋ H)` in a `?`-context.
  --
  -- Also consider using the already proven duality lemma `bang_neg`/`quest_neg` (available from imports, even if not a blueprint dependency) to transport the problem to a statement about `ʔ`.
  sorry

theorem quest_neg_set (M : Type*) [PhaseSpace M] (G : Fact M) :
((PhaseSpace.Fact.quest (P:=M) (Gᗮ) : Fact M) : Set M) =
((PhaseSpace.Fact.bang (P:=M) G : Fact M) : Set M)⫠ := by
calc
    ((PhaseSpace.Fact.quest (P := M) (Gᗮ) : Fact M) : Set M)
        = (((Gᗮ : Set M)⫠ ∩ PhaseSpace.I) : Set M)⫠ := by
            simp only [PhaseSpace.Fact.quest, dualFact_coe]
    _ = (((G : Set M)⫠⫠ ∩ PhaseSpace.I) : Set M)⫠ := by
            simp only [Fact.coe_neg]
    _ = (((G : Set M) ∩ PhaseSpace.I) : Set M)⫠ := by
            simpa
            [PhaseSpace.isFact] using
            congrArg (fun S : Set M => (S ∩ PhaseSpace.I)⫠) G.property.symm
    _ = ((PhaseSpace.Fact.bang (P := M) G : Fact M) : Set M)⫠ := by
            simp only [PhaseSpace.Fact.bang, dualFact_coe, PhaseSpace.triple_orth]

theorem quest_neg (M : Type*) [PhaseSpace M] (G : Fact M) : (ʔ (Gᗮ) : Fact M) =
( ! G : Fact M)ᗮ := by
  apply SetLike.coe_injective
  simp [quest_neg_set]

theorem bang_neg (M : Type*) [PhaseSpace M] (G : Fact M) : ( ! (Gᗮ) : Fact M) =
(ʔ G : Fact M)ᗮ := by
  have h := quest_neg (M := M) (G := (Gᗮ : Fact M))
  have h' := congrArg (fun H : Fact M => (Hᗮ)) h
  simpa using h'.symm


theorem interpProp_dual (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A : Proposition Atom) :
(interpProp (Atom:=Atom) (M:=M) v (A⫠) : Fact M) = (interpProp (Atom:=Atom) (M:=M) v A)ᗮ := by
  induction A with
  | atom a =>
      simp [PhaseSpace.interpProp, Proposition.dual]
  | atomDual a =>
      simp [PhaseSpace.interpProp, Proposition.dual]
  | one =>
      simp [PhaseSpace.interpProp, Proposition.dual]
  | zero =>
      simp [PhaseSpace.interpProp, Proposition.dual]
  | top =>
      simp [PhaseSpace.interpProp, Proposition.dual]
  | bot =>
      simp [PhaseSpace.interpProp, Proposition.dual]
  | tensor A B ihA ihB =>
      simp [PhaseSpace.interpProp, Proposition.dual, ihA, ihB, neg_tensor]
  | parr A B ihA ihB =>
      simp [PhaseSpace.interpProp, Proposition.dual, ihA, ihB, neg_par]
  | oplus A B ihA ihB =>
      simp [PhaseSpace.interpProp, Proposition.dual, ihA, ihB, neg_plus]
  | «with» A B ihA ihB =>
      simp [PhaseSpace.interpProp, Proposition.dual, ihA, ihB, neg_with]
  | bang A ih =>
      simpa [PhaseSpace.interpProp, Proposition.dual, ih] using
        (quest_neg (M := M) (G := interpProp (Atom:=Atom) (M:=M) v A))
  | quest A ih =>
      simpa [PhaseSpace.interpProp, Proposition.dual, ih] using
        (bang_neg (M := M) (G := interpProp (Atom:=Atom) (M:=M) v A))

theorem ax_valid (M : Type*) [PhaseSpace M] (v : Atom → Fact M) (A : Proposition Atom) :
(interpProp (Atom:=Atom) (M:=M) v A ⅋ (interpProp (Atom:=Atom) (M:=M) v A)ᗮ : Fact M).IsValid := by
  change (1 : M) ∈
      (interpProp (Atom:=Atom) (M:=M) v A ⅋ (interpProp (Atom:=Atom) (M:=M) v A)ᗮ : Fact M)
  rw [Fact.par_of_linImpl]
  rw [Fact.linImpl_iff_implies]
  intro x hx
  simpa [PhaseSpace.imp, one_mul] using hx

theorem cut_valid (M : Type*) [PhaseSpace M] {v : Atom → Fact M} {A : Proposition Atom}
{Γ Δ : Sequent Atom} : (interpProp (Atom:=Atom) (M:=M) v A ⅋ interpSequent
(Atom:=Atom) M v Γ).IsValid → ((interpProp (Atom:=Atom) (M:=M) v A)ᗮ ⅋ interpSequent
(Atom:=Atom) M v Δ).IsValid → (interpSequent (Atom:=Atom) M v Γ ⅋ interpSequent
(Atom:=Atom) M v Δ).IsValid := by
  classical
  intro hΓ hΔ
  let PA : Fact M := interpProp (Atom:=Atom) (M:=M) v A
  let G : Fact M := interpSequent (Atom:=Atom) M v Γ
  let H : Fact M := interpSequent (Atom:=Atom) M v Δ
  have hPA : (PAᗮ : Set M) ⊆ (G : Set M) := by
    have h1 : (1 : M) ∈ (PAᗮ ⊸ G : Fact M) := by
      simpa [PA, G, Fact.par_of_linImpl] using hΓ
    have himp : imp (PAᗮ : Set M) (G : Set M) (1 : M) :=
      (Fact.linImpl_iff_implies (p := (1 : M)) (G := PAᗮ) (H := G)).1 h1
    intro x hx
    have hxG : (1 : M) * x ∈ (G : Set M) := himp x hx
    simpa [one_mul] using hxG
  have hAH : (PA : Set M) ⊆ (H : Set M) := by
    have h1 : (1 : M) ∈ (PA ⊸ H : Fact M) := by
      simpa [PA, H, Fact.par_of_linImpl] using hΔ
    have himp : imp (PA : Set M) (H : Set M) (1 : M) :=
      (Fact.linImpl_iff_implies (p := (1 : M)) (G := PA) (H := H)).1 h1
    intro x hx
    have hxH : (1 : M) * x ∈ (H : Set M) := himp x hx
    simpa [one_mul] using hxH
  have hGoal : (1 : M) ∈ (Gᗮ ⊸ H : Fact M) := by
    apply (Fact.linImpl_iff_implies (p := (1 : M)) (G := Gᗮ) (H := H)).2
    intro x hx
    have hxPA : x ∈ (PA : Set M) := by
      have horth : (G : Set M)⫠ ⊆ ((PAᗮ : Set M) : Set M)⫠ :=
        PhaseSpace.orth_antitone (P := M) (X := (PAᗮ : Set M)) (Y := (G : Set M)) hPA
      have hx' : x ∈ (G : Set M)⫠ := by
        simpa [Fact.coe_neg, G] using hx
      have hx'' : x ∈ ((PAᗮ : Set M) : Set M)⫠ := horth hx'
      have horthPA : ((PAᗮ : Set M) : Set M)⫠ = (PA : Set M) := by
        have htmp : (PA : Set M) = ((PAᗮ : Set M) : Set M)⫠ := by
          simpa [Fact.neg_neg (G := PA)] using (Fact.coe_neg (G := PAᗮ))
        exact htmp.symm
      simpa [PA] using (show x ∈ (PA : Set M) from by
        rw [← horthPA]
        exact hx'')
    have hxH : x ∈ (H : Set M) := hAH hxPA
    simpa [one_mul] using hxH
  simpa [G, H, Fact.par_of_linImpl] using hGoal

theorem quest_valid_of_valid {M : Type*} [PhaseSpace M] {G : Fact M} :
G.IsValid → (PhaseSpace.Fact.quest G).IsValid := by
  intro hG
  exact IsValid_monotone (quest_le (M := M) G) hG

theorem soundness (Γ : Sequent Atom) : Γ.Provable → ∀ (M : Type*) [PhaseSpace M]
(v : Atom → Fact M), (interpSequent (Atom:=Atom) M v Γ).IsValid := by
  intro hΓ M _ v
  classical
  rcases hΓ with ⟨p⟩
  induction p with
  | ax =>
      rename_i a
      have hpair : ({a, a⫠} : Sequent Atom) = a ::ₘ ({a⫠} : Sequent Atom) := by simp
      have hsingle :
          interpSequent (Atom := Atom) M v ({a⫠} : Sequent Atom) =
            (interpProp (Atom := Atom) (M := M) v a)ᗮ := by
        have : ({a⫠} : Sequent Atom) = a⫠ ::ₘ (0 : Sequent Atom) := by simp
        -- compute the singleton sequent interpretation without unfolding orthogonals
        rw [this, interpSequent_cons, interpSequent_nil]
        -- `⟦a⫠⟧ ⅋ ⊥ = ⟦a⫠⟧ = (⟦a⟧)ᗮ`
        rw [par_bot]
        simpa using (interpProp_dual (Atom := Atom) (M := M) (v := v) (A := a))
      -- rewrite `interpSequent {a, a⫠}` to `⟦a⟧ ⅋ ⟦a⟧ᗮ` and apply `ax_valid`
      simpa [hpair, interpSequent_cons, hsingle] using
        (ax_valid (Atom := Atom) (M := M) (v := v) (A := a))
  | cut p q ihp ihq =>
      rename_i a Γ Δ
      have hΓ :
          (interpProp (Atom := Atom)
          (M := M) v a ⅋ interpSequent (Atom := Atom) M v Γ).IsValid := by
        simpa [interpSequent_cons] using ihp
      have hΔ :
          ((interpProp (Atom := Atom)
          (M := M) v a)ᗮ ⅋ interpSequent (Atom := Atom) M v Δ).IsValid := by
        simpa [interpSequent_cons, interpProp_dual] using ihq
      have hcut :
          (interpSequent (Atom := Atom) M v Γ ⅋ interpSequent (Atom := Atom) M v Δ).IsValid :=
        cut_valid (Atom := Atom) (M := M) (v := v) (A := a) (Γ := Γ) (Δ := Δ) hΓ hΔ
      simpa [interpSequent_add] using hcut
  | one =>
      have hs : ({(1 : Proposition Atom)} : Sequent Atom) =
      (1 : Proposition Atom) ::ₘ (0 : Sequent Atom) := by
        simp
      rw [hs, interpSequent_cons, interpSequent_nil]
      have hone :
          (interpProp (Atom := Atom)
          (M := M) v (1 : Proposition Atom) : Fact M) = (1 : Fact M) := by
        simp_all only [Multiset.cons_zero]
        rfl
      rw [hone, par_bot]
      simp [Fact.IsValid]
  | bot p ih =>
      rename_i Γ
      -- `interpSequent (⊥ ::ₘ Γ) = ⟦⊥⟧ ⅋ interpSequent Γ = ⊥ ⅋ interpSequent Γ = interpSequent Γ`.
      rw [interpSequent_cons]
      -- simplify `⟦⊥⟧v` to `⊥`
      have hbot : (interpProp (Atom := Atom)
      (M := M) v (⊥ : Proposition Atom) : Fact M) = (⊥ : Fact M) := by
        simpa using (interpProp_bot (Atom := Atom) (M := M) (v := v))
      rw [hbot]
      simpa [bot_par] using ih
  | parr p ih =>
      rename_i a b Γ
      simpa [interpSequent_cons, interpProp_parr, par_assoc] using ih
  | tensor p q ihp ihq =>
      rename_i a Γ b Δ
      let A : Fact M := interpProp (Atom := Atom) (M := M) v a
      let B : Fact M := interpProp (Atom := Atom) (M := M) v b
      let G : Fact M := interpSequent (Atom := Atom) M v Γ
      let H : Fact M := interpSequent (Atom := Atom) M v Δ
      have hAG : (A ⅋ G).IsValid := by
        simpa [A, G, interpSequent_cons] using ihp
      have hBH : (B ⅋ H).IsValid := by
        simpa [B, H, interpSequent_cons] using ihq
      have hA : (Aᗮ : Set M) ⊆ (G : Set M) := by
        have h1 : (1 : M) ∈ (Aᗮ ⊸ G : Fact M) := by
          simpa [A, G, par_of_linImpl] using hAG
        have himp : imp (Aᗮ : Set M) (G : Set M) (1 : M) :=
          (linImpl_iff_implies (p := (1 : M)) (G := Aᗮ) (H := G)).1 h1
        intro x hx
        have : (1 : M) * x ∈ (G : Set M) := himp x hx
        simpa [one_mul] using this
      have hB : (Bᗮ : Set M) ⊆ (H : Set M) := by
        have h1 : (1 : M) ∈ (Bᗮ ⊸ H : Fact M) := by
          simpa [B, H, par_of_linImpl] using hBH
        have himp : imp (Bᗮ : Set M) (H : Set M) (1 : M) :=
          (linImpl_iff_implies (p := (1 : M)) (G := Bᗮ) (H := H)).1 h1
        intro x hx
        have : (1 : M) * x ∈ (H : Set M) := himp x hx
        simpa [one_mul] using this
      have hA_le : (Aᗮ : Fact M) ≤ G := fun _ hx => hA hx
      have hB_le : (Bᗮ : Fact M) ≤ H := fun _ hx => hB hx
      have hpar : (Aᗮ ⅋ Bᗮ : Fact M) ≤ (G ⅋ H) := par_le_par hA_le hB_le
      have himp :
          imp ((Aᗮ ⅋ Bᗮ : Fact M) : Set M) ((G ⅋ H : Fact M) : Set M) (1 : M) := by
        intro x hx
        have : x ∈ (G ⅋ H : Fact M) := hpar hx
        simpa [one_mul] using this
      have hlin :
          (1 : M) ∈ ((Aᗮ ⅋ Bᗮ : Fact M) ⊸ (G ⅋ H : Fact M) : Fact M) :=
        (linImpl_iff_implies (p := (1 : M)) (G := (Aᗮ ⅋ Bᗮ : Fact M))
        (H := (G ⅋ H : Fact M))).2 himp
      have hgoal : ((A ⊗ B) ⅋ (G ⅋ H) : Fact M).IsValid := by
        have : (1 : M) ∈ (((A ⊗ B) ⅋ (G ⅋ H) : Fact M) : Set M) := by
          simpa [par_of_linImpl, neg_tensor] using hlin
        exact this
      simpa [interpSequent_cons, interpSequent_add,
      interpProp_tensor, A, B, G, H, par_assoc] using hgoal
  | oplus₁ p ih =>
      rename_i a Γ b
      have h :
          (interpProp (Atom := Atom)
          (M := M) v a ⅋ interpSequent (Atom := Atom) M v Γ).IsValid := by
        simpa [interpSequent_cons] using ih
      have ha :
          (interpProp (Atom := Atom) (M := M) v a : Fact M) ≤
            (interpProp (Atom := Atom) (M := M) v (a ⊕ b) : Fact M) := by
        simpa [interpProp_oplus (Atom := Atom) (M := M) v a b] using
          (le_plus_left (G := (interpProp (Atom := Atom) (M := M) v a : Fact M))
            (H := (interpProp (Atom := Atom) (M := M) v b : Fact M)))
      have hpar :
          (interpProp (Atom := Atom) (M := M) v a ⅋ interpSequent (Atom := Atom) M v Γ : Fact M) ≤
            (interpProp (Atom := Atom)
            (M := M) v (a ⊕ b) ⅋ interpSequent (Atom := Atom) M v Γ : Fact M) :=
        par_le_par ha (le_rfl)
      have := IsValid_monotone (M := M) hpar h
      simpa [interpSequent_cons, interpProp_oplus] using this
  | oplus₂ p ih =>
      rename_i a Γ b
      have h :
          (interpProp (Atom := Atom)
          (M := M) v a ⅋ interpSequent (Atom := Atom) M v Γ).IsValid := by
        simpa [interpSequent_cons] using ih
      have ha :
          (interpProp (Atom := Atom) (M := M) v a : Fact M) ≤
            (interpProp (Atom := Atom) (M := M) v (a ⊕ b) : Fact M) := by
        simpa [interpProp_oplus (Atom := Atom) (M := M) v a b] using
          (le_plus_left (G := (interpProp (Atom := Atom) (M := M) v a : Fact M))
            (H := (interpProp (Atom := Atom) (M := M) v b : Fact M)))
      have hpar :
          (interpProp (Atom := Atom) (M := M) v a ⅋ interpSequent (Atom := Atom) M v Γ : Fact M) ≤
            (interpProp (Atom := Atom)
            (M := M) v (a ⊕ b) ⅋ interpSequent (Atom := Atom) M v Γ : Fact M) :=
        par_le_par ha (le_rfl)
      have := IsValid_monotone (M := M) hpar h
      simpa [interpSequent_cons, interpProp_oplus, plus_comm] using this
  | «with» p q ihp ihq =>
      rename_i a Γ b
      have ha :
          (interpProp (Atom := Atom)
          (M := M) v a ⅋ interpSequent (Atom := Atom) M v Γ).IsValid := by
        simpa [interpSequent_cons] using ihp
      have hb :
          (interpProp (Atom := Atom)
          (M := M) v b ⅋ interpSequent (Atom := Atom) M v Γ).IsValid := by
        simpa [interpSequent_cons] using ihq
      have : ((interpProp (Atom := Atom) (M := M) v (a & b) : Fact M) ⅋
          interpSequent (Atom := Atom) M v Γ).IsValid := by
        simpa [interpProp_with, with_par_distrib] using (And.intro ha hb)
      simpa [interpSequent_cons, interpProp_with] using this
  | top =>
      rename_i Γ
      -- `⊤ ⅋ G = ⊤` and `⊤` is valid
      rw [interpSequent_cons]
      have htop : (interpProp (Atom := Atom)
      (M := M) v (⊤ : Proposition Atom) : Fact M) = (⊤ : Fact M) := by
        simpa using (interpProp_top (Atom := Atom) (M := M) (v := v))
      rw [htop]
      simp [top_par, Fact.IsValid]
  | quest p ih =>
      rename_i a Γ
      have h :
          (interpProp (Atom := Atom)
          (M := M) v a ⅋ interpSequent (Atom := Atom) M v Γ).IsValid := by
        simpa [interpSequent_cons] using ih
      have hle :
          (interpProp (Atom := Atom) (M := M) v a ⅋ interpSequent (Atom := Atom) M v Γ : Fact M) ≤
            (PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
              interpSequent (Atom := Atom) M v Γ : Fact M) :=
        par_le_par (quest_le (M := M) (G := interpProp (Atom := Atom) (M := M) v a)) (le_rfl)
      have := IsValid_monotone (M := M) hle h
      simpa [interpSequent_cons, interpProp_quest] using this
  | weaken p ih =>
      rename_i Γ a
      have h : (interpSequent (Atom := Atom) M v Γ).IsValid := ih
      have hle :
          (interpSequent (Atom := Atom) M v Γ : Fact M) ≤
            (PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
              interpSequent (Atom := Atom) M v Γ : Fact M) := by
        simpa [bot_par] using
          (par_le_par (bot_le_quest (M := M) (G := interpProp (Atom := Atom) (M := M) v a))
            (le_rfl) : ((⊥ : Fact M) ⅋ interpSequent (Atom := Atom) M v Γ : Fact M) ≤ _)
      have := IsValid_monotone (M := M) hle h
      simpa [interpSequent_cons, interpProp_quest] using this
  | contract p ih =>
      rename_i a Γ
      have h :
          (PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
              (PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
                interpSequent (Atom := Atom) M v Γ) : Fact M).IsValid := by
        simpa [interpSequent_cons, interpProp_quest, par_assoc] using ih
      have hle :
          (PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
              (PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
                interpSequent (Atom := Atom) M v Γ) : Fact M)
            ≤
          (PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
              interpSequent (Atom := Atom) M v Γ : Fact M) := by
        have h' :
            ((PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
                  PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a)) ⅋
                interpSequent (Atom := Atom) M v Γ : Fact M)
              ≤
            (PhaseSpace.Fact.quest (interpProp (Atom := Atom) (M := M) v a) ⅋
                interpSequent (Atom := Atom) M v Γ : Fact M) :=
          par_le_par (quest_contract_le (M := M) (G := interpProp (Atom := Atom) (M := M) v a))
          (le_rfl)
        simpa [par_assoc] using h'
      have := IsValid_monotone (M := M) hle h
      simpa [interpSequent_cons, interpProp_quest] using this
  | bang hQuestCtx p ih =>
      rename_i Δ A
      have h :
          (interpProp (Atom := Atom)
          (M := M) v A ⅋ interpSequent (Atom := Atom) M v Δ).IsValid := by
        simpa [interpSequent_cons] using ih
      have := bang_valid_of_allQuest (Atom := Atom) (M := M) (v := v) (a := A) (Γ := Δ) hQuestCtx h
      simpa [interpSequent_cons, interpProp_bang] using this

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
