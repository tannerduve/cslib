/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Cslib.Control.Monad.Free
import Mathlib.Tactic.Cases
/-!
# Free Monad Example: Verified Interpreter

This file gives an example of free monads in use by implementing an interpreter for a
simple effectful expression language using free monads. The language supports arithmetic,
variables, and three effects: state, errors, and tracing.

## Components

**Separation of Syntax and Semantics**: Free monads let us separate *what* we want to do
(syntactic description of effectful computation) from *how* we want to do it (interpreting
and executing effects semantically).

**Effect Composability**: Multiple effects (state, errors, tracing) can be combined
cleanly using sum types without monad transformer complexity.

**Formal Verification**: The separation enables proving correctness by relating
the catamorphic interpreter to an operational semantics.

## Contents

1. **Expression Language**: Simple arithmetic with variables
2. **Effect Definitions**: State, errors, and tracing as separate effect types
3. **Effect Combination**: Sum types to compose multiple effects
4. **Syntax Tree Construction**: Helper functions to build `FreeM` programs
5. **Interpreter**: Fold-based interpreter into a concrete monad
6. **Operational Semantics**: Big-step semantics as an inductive relation
7. **Correctness Proof**: Formal verification that interpreter matches semantics

This example shows how free monads enable building domain-specific languages with
clean separation between syntax and semantics, enabling multiple interpretations
(execution, analysis, verification) of the same programs.

## References

Based on "Tutorial: A Verified Interpreter with Side Effects" demonstrating practical
applications of the mathematical theory developed in the core Free monad files.
-/

open FreeM

-- Expression Language
inductive Expr where
  | val : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | div : Expr → Expr → Expr

-- Environment: variable bindings
abbrev Env := List (String × Int)

-- Effect Types
inductive StateEff : Type → Type where
  | Get : StateEff Env
  | Put : Env → StateEff Unit

inductive ErrorEff : Type → Type where
  | Fail : String → ErrorEff Unit

inductive TraceEff : Type → Type where
  | Log : String → TraceEff Unit

-- Effect Sum Types
inductive FSum (F G : Type → Type) (α : Type) where
  | inl : F α → FSum F G α
  | inr : G α → FSum F G α

infixl:50 "⊕" => FSum

-- Combined Effect Signature
abbrev Eff := StateEff ⊕ (ErrorEff ⊕ TraceEff)

-- Helper Functions for Effect Construction
def getEnv : FreeM Eff Env :=
  lift (FSum.inl StateEff.Get)

def putEnv (e : Env) : FreeM Eff Unit :=
  lift (FSum.inl (StateEff.Put e))

def fail (msg : String) : FreeM Eff Unit :=
  lift (FSum.inr (FSum.inl (ErrorEff.Fail msg)))

def log (msg : String) : FreeM Eff Unit :=
  lift (FSum.inr (FSum.inr (TraceEff.Log msg)))

-- Example Program
def exampleProgram : FreeM Eff Int := do
  log "Starting computation"
  putEnv [("x", 10)]
  let env ← getEnv
  match env.find? (·.fst = "x") with
  | some (_, x) => pure (x + 1)
  | none => do
      fail "x not found"
      pure 0

-- Interpreter Infrastructure

abbrev Trace := List String

-- Semantic domain: stateful computation with errors and tracing
abbrev EffAction (α : Type) := Env → Trace → Except String (α × Env × Trace)

-- Catamorphism for FreeM (from Free/Fold.lean but specialized here)
def cataFreeM {F : Type u → Type v} {α β : Type w}
  (onValue : α → β)
  (onEffect : {ι : Type u} → F ι → (ι → β) → β)
  : FreeM F α → β
| .pure a => onValue a
| .liftBind op k => onEffect op (fun x => cataFreeM onValue onEffect (k x))

-- Algebra components for our effect domain
def effPure {α} (a : α) : EffAction α :=
  fun env tr => .ok (a, env, tr)

def effStep {α} :
    {ι : Type} → Eff ι → (ι → EffAction α) → EffAction α
  | _, .inl StateEff.Get, k => fun env tr => k env env tr
  | _, .inl (StateEff.Put σ), k => fun _ tr => k () σ tr
  | _, .inr (.inl (ErrorEff.Fail msg)), _ => fun _ _ => .error msg
  | _, .inr (.inr (TraceEff.Log msg)), k => fun env tr => k () env (tr ++ [msg])

-- Complete interpreter via catamorphism
def runEff {α} : FreeM Eff α → EffAction α :=
  cataFreeM effPure effStep

-- Operational Semantics

-- Big-step operational semantics as inductive relation
inductive EvalRel : Expr → Env → Trace → Except String (Int × Env × Trace) → Prop where
| val :
    ∀ n env trace,
    EvalRel (.val n) env trace (.ok (n, env, trace))
| var_found :
    ∀ x env trace v,
    env.find? (·.fst = x) = some (x, v) →
    EvalRel (.var x) env trace (.ok (v, env, trace))
| var_missing :
    ∀ x env trace,
    env.find? (·.fst = x) = none →
    EvalRel (.var x) env trace (.error s!"unbound variable {x}")
| add :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.add e1 e2) env trace₁ (.ok (v1 + v2, env₃, trace₃))
| div_ok :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    v2 ≠ 0 →
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.div e1 e2) env trace₁ (.ok (v1 / v2, env₃, trace₃))
| div_zero :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    v2 = 0 →
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.div e1 e2) env trace₁ (.error "divide by zero")

-- Evaluator: constructs FreeM syntax trees from expressions
def eval : Expr → FreeM Eff Int
  | .val n => pure n
  | .var x => do
      let env ← getEnv
      match env.find? (·.fst = x) with
      | some (_, v) => pure v
      | none => do
          fail s!"unbound variable {x}"
          pure 0
  | .add e1 e2 => do
      let v1 ← eval e1
      let v2 ← eval e2
      pure (v1 + v2)
  | .div e1 e2 => do
      let v1 ← eval e1
      let v2 ← eval e2
      if v2 = 0 then do
        fail "divide by zero"
        pure 0
      else
        pure (v1 / v2)

-- Correctness Proofs

-- Helper lemmas for bind behavior
theorem runEff_bind_ok {α β}
    {p : FreeM Eff α} {k : α → FreeM Eff β}
    {env env' : Env} {tr tr' : Trace} {v : α}
    (h : runEff p env tr = .ok (v, env', tr')) :
    runEff (p >>= k) env tr = runEff (k v) env' tr' := by
  revert env env' tr tr' v
  induction p <;> simp only [runEff, bind, cataFreeM]
  · case pure a =>
    intros env env' tr tr' v h
    simp only [effPure] at h
    injection h with a_eq
    cases a_eq
    rfl
  · case liftBind ι op cont ih =>
    intros env env' tr tr' v h
    cases op
    · case inl s =>
      cases s
      case Get => apply ih; exact h
      case Put => apply ih; exact h
    · case inr s =>
      cases s
      case inl s =>
        cases s
        case Fail => simp [effStep] at *
      case inr s =>
        cases s
        case Log => apply ih; exact h

theorem runEff_bind_err {α β}
    {p : FreeM Eff α} {k : α → FreeM Eff β}
    {env : Env} {tr : Trace} {msg : String} :
  runEff p env tr = .error msg →
  runEff (p >>= k) env tr = .error msg := by
  revert env tr msg
  induction p <;> simp only [runEff, bind, cataFreeM]
  · case pure a =>
    intros env tr msg h
    simp [effPure] at h
  · case liftBind ι op cont ih =>
    intros env tr msg h
    cases op
    · case inl s =>
      cases s
      case Get => apply ih; exact h
      case Put => apply ih; exact h
    · case inr s =>
      cases s
      case inl s =>
        cases s
        case Fail msg' =>
          simp only [effStep] at h
          injection h with msg_eq
          cases msg_eq
          rfl
      case inr s =>
        cases s
        case Log msg' => apply ih; exact h

-- Main correctness theorem: interpreter agrees with operational semantics
theorem runEff_eval_correct (e : Expr) (env : Env) (trace : Trace)
    (res : Except String (Int × Env × Trace))
    (h : EvalRel e env trace res) :
    runEff (eval e) env trace = res := by
    induction' h
    · case val z env trace =>
      simp [eval, pure_eq_pure, runEff, cataFreeM, effPure]
    · case var_found x env trace v h =>
      simp [runEff, eval, getEnv, lift_def, cataFreeM, effStep, h, effPure]
    · case var_missing x env trace h =>
      simp [runEff, eval, bind, getEnv, fail, lift_def, cataFreeM, effStep, h]
    · case add e₁ e₂ env trace₁ trace₂ trace₃ v1 v2 env₂ env₃ h₁ h₂ ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁ ) (k := fun v1 => do
        let v2 ← eval e₂
        pure (v1 + v2)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v2 => pure (v1 + v2)) ih₂
      simp [bind] at step₂; simp [step₂]; congr
    · case div_ok e₁ e₂ env trace₁ trace₂ trace₃ v₁ v₂ env₂ env₃ v₂_ne_0 h₁ h₂ ih₁ ih₂  =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁) (k := fun v1 => do
        let v2 ← eval e₂
        if v2 = 0 then do fail "divide by zero"; pure 0 else pure (v1 / v2)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v₂ =>
        if v₂ = 0 then do fail "divide by zero"; pure 0 else pure (v₁ / v₂)) ih₂
      simp [bind] at step₂; simp [step₂, v₂_ne_0]
      congr
    · case div_zero e₁ e₂ env' trace₁ trace₂ trace₃ v₁ v₂ env₂ env₃ v₂_eq_0 h₁ h₂ ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁) (k := fun v₁ => do
        let v₂ ← eval e₂
        if v₂ = 0 then fail "divide by zero"; pure 0 else pure (v₁ / v₂)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v₂ =>
        if v₂ = 0 then (do fail "divide by zero"; pure 0) else pure (v₁ / v₂)) ih₂
      simp [bind] at step₂; simp [step₂, v₂_eq_0]
      simp [fail, lift, runEff]
      congr
