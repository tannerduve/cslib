import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic
import Aesop
import Cslib.Logics.LinearLogic.CLL.Basic

/-!
# Phase semantics for CLL

This file defines the phase semantics for CLL.
-/

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

notation:99 X"ᗮ" => PhaseSpace.orthogonal X

structure Fact (M : Type u) [PhaseSpace M] where
  carrier : Set M
  closed  : carrier = (carrierᗮ)ᗮ

instance [PhaseSpace M] : Coe (Fact M) (Set M) where
  coe F := F.carrier

def interp [PhaseSpace M] (P : Proposition Atom) (v : Atom → Fact M) : Set M :=
  match P with
  | atom x => v x
  | atomDual x => (v x)ᗮ
  | one => {1}ᗮᗮ
  | zero => ∅ᗮᗮ
  | top => fun _ => True
  | Proposition.bot => fun _ => False
  | X ⊗ Y => {m * n | m ∈ interp X v ∧ n ∈ interp Y v}




end PhaseSpace

end CLL
