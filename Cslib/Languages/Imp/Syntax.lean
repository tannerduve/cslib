/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Mathlib.Logic.Function.Basic

/-!
# IMP Syntax

This file defines the abstract syntax of the IMP language, as well as a macro system for
constructing IMP programs. IMP is a simple imperative language with assignment, conditionals,
and while loops.

## Main definitions

- `aexp`: arithmetic expressions
- `bexp`: boolean expressions
- `Stmt`: commands in IMP

## References

- [Pierce et al., *Software Foundations*][PierceEtAl2025]
- [Baanen et al., *The Hitchhiker's Guide to Logical Verification*][BaanenEtAl2018]
-/

namespace Imp

abbrev Val := ℤ

abbrev State := String → Val

/--
Arithmetic expressions
-/
inductive aexp : Type where
  | ANum (n : ℤ)
  | AId (x : String)
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
Commands in IMP
-/
inductive Stmt : Type where
| Cskip : Stmt
| Cassign : (x : String) → (a : aexp) → Stmt
| Cseq : Stmt → Stmt → Stmt
| CifThenElse : (b : bexp) → Stmt → Stmt → Stmt
| CwhileDo : (b : bexp) → Stmt → Stmt

-- Software Foundations style notation system

instance : Coe ℤ aexp where coe := aexp.ANum
instance : Coe String aexp where coe := aexp.AId

declare_syntax_cat imp_lang

-- Grammar rules for the Imp language
syntax num : imp_lang
syntax ident : imp_lang
syntax "(" imp_lang ")" : imp_lang

-- Arithmetic operations
syntax imp_lang " + " imp_lang : imp_lang
syntax imp_lang " - " imp_lang : imp_lang
syntax imp_lang " × " imp_lang : imp_lang
syntax imp_lang " * " imp_lang : imp_lang

-- Boolean constants and operations
syntax "true" : imp_lang
syntax "false" : imp_lang
syntax imp_lang " = " imp_lang : imp_lang
syntax imp_lang " ≠ " imp_lang : imp_lang
syntax imp_lang " ≤ " imp_lang : imp_lang
syntax imp_lang " > " imp_lang : imp_lang
syntax "¬ " imp_lang : imp_lang
syntax imp_lang " && " imp_lang : imp_lang

-- Command syntax
syntax "skip" : imp_lang
syntax ident " := " imp_lang : imp_lang
syntax imp_lang " ; " imp_lang : imp_lang
syntax "if " imp_lang " then " imp_lang " else " imp_lang " end" : imp_lang
syntax "while " imp_lang " do " imp_lang " end" : imp_lang

-- The main <{ ... }> notation
syntax "<{ " imp_lang " }>" : term

syntax "⟦" term "⟧" : imp_lang

macro_rules
  -- Numbers and identifiers
  | `(<{ $n:num }>) => `(aexp.ANum $n)
  | `(<{ $x:ident }>) => `(aexp.AId $(Lean.quote (toString x.getId)))
  | `(<{ ( $e ) }>) => `(<{ $e }>)

  -- Arithmetic operations
  | `(<{ $a + $b }>) => `(aexp.APlus <{ $a }> <{ $b }>)
  | `(<{ $a - $b }>) => `(aexp.AMinus <{ $a }> <{ $b }>)
  | `(<{ $a × $b }>) => `(aexp.AMult <{ $a }> <{ $b }>)
  | `(<{ $a * $b }>) => `(aexp.AMult <{ $a }> <{ $b }>)

  -- Boolean constants and operations
  | `(<{ true }>) => `(bexp.BTrue)
  | `(<{ false }>) => `(bexp.BFalse)
  | `(<{ $a = $b }>) => `(bexp.BEq <{ $a }> <{ $b }>)
  | `(<{ $a ≠ $b }>) => `(bexp.BNeq <{ $a }> <{ $b }>)
  | `(<{ $a ≤ $b }>) => `(bexp.BLe <{ $a }> <{ $b }>)
  | `(<{ $a > $b }>) => `(bexp.BGt <{ $a }> <{ $b }>)
  | `(<{ ¬ $b }>) => `(bexp.BNot <{ $b }>)
  | `(<{ $a && $b }>) => `(bexp.BAnd <{ $a }> <{ $b }>)

  -- Commands
  | `(<{ skip }>) => `(Stmt.Cskip)

-- Additional macro rules for more complex syntax
macro_rules
  | `(<{ $x:ident := $a }>) => `(Stmt.Cassign $(Lean.quote (toString x.getId)) <{ $a }>)

macro_rules
  | `(<{ $c₁ ; $c₂ }>) => `(Stmt.Cseq <{ $c₁ }> <{ $c₂ }>)

macro_rules
  | `(<{ if $b then $c₁ else $c₂ end }>) => `(Stmt.CifThenElse <{ $b }> <{ $c₁ }> <{ $c₂ }>)

macro_rules
  | `(<{ while $b do $c end }>) => `(Stmt.CwhileDo <{ $b }> <{ $c }>)

macro_rules
  | `(<{ ⟦ $t:term ⟧ }>) => `($t)

infixr:90 " ; " => Stmt.Cseq

end Imp
