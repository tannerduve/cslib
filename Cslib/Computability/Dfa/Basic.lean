/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.Lts.Basic

/-! # Deterministic Finite-State Automata

A Deterministic Finite-State Automaton (DFA) is a finite-state machine that accepts or rejects
a finite string.
-/

/-- A Deterministic Finite-State Automaton (DFA) consists of a labelled transition function
`tr` over finite sets of states and labels (called symbols), a starting state `start` and a finite
set of accepting states `accept`. -/
structure Dfa (State : Type _) (Symbol : Type _) where
  /-- The transition function of the automaton. -/
  tr : State → Symbol → State
  /-- Start state. -/
  start : State
  /-- Accept states. -/
  accept : Finset State
  /-- The automaton is finite-state. -/
  finite_state : Finite State
  /-- The type of symbols (also called 'alphabet') is finite. -/
  finite_symbol : Finite Symbol

namespace Dfa

/-- `Dfa` is a special case of `Lts`. -/
@[grind]
def toLts (dfa : Dfa State Symbol) : Lts State Symbol :=
  Lts.mk (fun s1 μ s2 => dfa.tr s1 μ = s2)

instance : Coe (Dfa State Symbol) (Lts State Symbol) where
  coe := toLts

@[grind]
theorem toLts_tr {dfa : Dfa State Symbol} :
  dfa.toLts.Tr s1 μ s2 ↔ dfa.tr s1 μ = s2 := by
  rfl

/-- The LTS induced by a DFA is deterministic. -/
@[grind]
theorem toLts_deterministic (dfa : Dfa State Symbol) : dfa.toLts.Deterministic := by
  grind

/-- The LTS induced by a DFA is finite-state. -/
@[grind]
theorem toLts_finiteState (dfa : Dfa State Symbol) : dfa.toLts.FiniteState :=
  dfa.finite_state

/-- A DFA accepts a trace if there is a multi-step accepting derivative with that trace from
the start state. -/
@[grind]
def Accepts (dfa : Dfa State Symbol) (μs : List Symbol) :=
  ∃ s ∈ dfa.accept, dfa.toLts.MTr dfa.start μs s

/-- The language of a DFA is the set of traces that it accepts. -/
@[grind]
def language (dfa : Dfa State Symbol) : Set (List Symbol) :=
  { μs | dfa.Accepts μs }

/-- A trace is accepted by a DFA iff it is in the language of the DFA. -/
@[grind]
theorem accepts_mem_language (dfa : Dfa State Symbol) (μs : List Symbol) :
  dfa.Accepts μs ↔ μs ∈ dfa.language := by rfl

end Dfa
