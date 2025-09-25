/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Cslib.Languages.Imp.Syntax
import Aesop

/-!
# Big-step Operational Semantics for IMP

This file defines and proves determinism of the big-step operational semantics for IMP.

## References

- [Pierce et al., *Software Foundations*][PierceEtAl2025]
- [Baanen et al., *The Hitchhiker's Guide to Logical Verification*][BaanenEtAl2018]
-/

namespace Imp

open Function

/--
Evaluate an arithmetic expression in a given state.
-/
def aexp_eval (st : State) (a : aexp) : Val :=
  match a with
  | aexp.ANum n => n
  | aexp.AId x => st x
  | aexp.APlus a1 a2 => aexp_eval st a1 + aexp_eval st a2
  | aexp.AMinus a1 a2 => aexp_eval st a1 - aexp_eval st a2
  | aexp.AMult a1 a2 => aexp_eval st a1 * aexp_eval st a2

/--
Evaluate a boolean expression in a given state.
-/
def bexp_eval (st : State) (b : bexp) : Prop :=
  match b with
  | bexp.BTrue => True
  | bexp.BFalse => False
  | bexp.BEq a1 a2 => aexp_eval st a1 = aexp_eval st a2
  | bexp.BNeq a1 a2 => aexp_eval st a1 ≠ aexp_eval st a2
  | bexp.BLe a1 a2 => aexp_eval st a1 ≤ aexp_eval st a2
  | bexp.BGt a1 a2 => aexp_eval st a1 > aexp_eval st a2
  | bexp.BNot b => ¬ bexp_eval st b
  | bexp.BAnd b1 b2 => bexp_eval st b1 ∧ bexp_eval st b2

/--
Big-step operational semantics for IMP
-/
inductive BigStep : Stmt × State → State → Prop where
| Bskip (s) :
  BigStep (Stmt.Cskip, s) s
| Bassign (x a s) :
  BigStep (Stmt.Cassign x a, s) (update s x (aexp_eval s a))
| Bseq (S T s t u) (hS : BigStep (S, s) t) (hT : BigStep (T, t) u) :
  BigStep (Stmt.Cseq S T, s) u
| Bif_true (B S T s t) (hcond : bexp_eval s B) (hbody : BigStep (S, s) t) :
  BigStep (Stmt.CifThenElse B S T, s) t
| Bif_false (B S T s t) (hcond : ¬ bexp_eval s B) (hbody : BigStep (T, s) t) :
  BigStep (Stmt.CifThenElse B S T, s) t
| Bwhile_true (B S s t u) (hcond : bexp_eval s B) (hbody : BigStep (S, s) t)
  (hrest : BigStep (Stmt.CwhileDo B S, t) u) :
  BigStep (Stmt.CwhileDo B S, s) u
| Bwhile_false (B S s) (hcond : ¬ bexp_eval s B) :
  BigStep (Stmt.CwhileDo B S, s) s
infix:110 " ⟹ " => BigStep

/--
The big-step operational semantics for IMP is deterministic.
-/
theorem BigStep_deterministic {Ss l r} (hl : Ss ⟹ l)
      (hr : Ss ⟹ r) :
    l = r :=
  by
    induction hl generalizing r with
    | Bskip s =>
      cases hr with
      | Bskip => rfl
    | Bassign x a s =>
      cases hr with
      | Bassign => rfl
    | Bseq S T s l₀ l hS hT ihS ihT =>
      cases hr with
      | Bseq _ _ _ r₀ _ hS' hT' =>
        cases ihS hS' with
        | refl =>
          cases ihT hT' with
          | refl => rfl
    | Bif_true B S T s l hB hS ih =>
      cases hr with
      | Bif_true _ _ _ _ _ hB' hS'  => apply ih hS'
      | Bif_false _ _ _ _ _ hB' hS' => aesop
    | Bif_false B S T s l hB hT ih =>
      cases hr with
      | Bif_true _ _ _ _ _ hB' hS'  => aesop
      | Bif_false _ _ _ _ _ hB' hS' => apply ih hS'
    | Bwhile_true B S s l₀ l hB hS hw ihS ihw =>
      cases hr with
      | Bwhile_true _ _ _ r₀ hB' hB' hS' hw' =>
        cases ihS hS' with
        | refl =>
          cases ihw hw' with
          | refl => rfl
      | Bwhile_false _ _ _ hB' => aesop
    | Bwhile_false B S s hB =>
      cases hr with
      | Bwhile_true _ _ _ s' _ hB' hS hw => aesop
      | Bwhile_false _ _ _ hB'           => rfl

end Imp
