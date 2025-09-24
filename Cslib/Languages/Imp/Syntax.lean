/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Std.Data.HashMap

open Std

/-!
# IMP Syntax

This file defines the abstract syntax of the IMP language. It is a simple imperative language with
assignment, conditional, and while loops.

## Main definitions

- `aexp`: arithmetic expressions
- `bexp`: boolean expressions
- `Stmt`: statements

## References

- [Pierce et al., *Software Foundations*][PierceEtAl2025]
- [Baanen et al., *The Hitchhiker's Guide to Logical Verification*][BaanenEtAl2018]

[PierceEtAl2025]: https://softwarefoundations.cis.upenn.edu
[BaanenEtAl2025]: https://lean-forward.github.io/hitchhikers-guide/2025
-/

abbrev Var := String

abbrev Val := Nat

abbrev State := Var → Val

/--
Arithmetic expressions
-/
inductive aexp : Type where
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)

/--
Boolean expressions
-/
inductive bexp : Type where
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)

/--
Statements
-/
inductive Stmt : Type where
| skip : Stmt
| assign : Var → (State → Nat) → Stmt
| seq : Stmt → Stmt → Stmt
| ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
| whileDo : (State → Prop) → Stmt → Stmt
