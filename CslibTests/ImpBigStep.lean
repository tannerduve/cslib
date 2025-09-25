import Cslib.Languages.Imp.OpSem.BigStep

open Imp

-- Examples using SF notation

def plus2 : Stmt :=
  <{ X := X + 2 }>

def XtimesYinZ : Stmt :=
  <{ Z := X × Y }>

lemma plus2_spec
  (st st' : State) (n : ℤ)
  (hX : st "X" = n)
  (hev : (plus2, st) ⟹ st') :
  st' "X" = n + 2 := by
  cases hev
  simp [aexp_eval, hX]

lemma XtimesYinZ_spec
  (st st' : State) (n m : ℤ)
  (hX : st "X" = n)
  (hY : st "Y" = m)
  (hev : (XtimesYinZ, st) ⟹ st') :
  st' "Z" = n * m := by
  cases hev
  simp [aexp_eval, hX, hY]
