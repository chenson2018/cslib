/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.LocallyNameless.Fsub.Basic

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

attribute [simp] Ty.open_tt_rec

lemma Ty.open_tt_rec_type_aux : forall (T : Ty Var) j V i U,
  i ≠ j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T := by
  intros T
  induction T <;> intros j V i U neq H
  case bvar i' => 
    by_cases eq : i = i' <;> [subst eq; skip] <;> simp_all only [neq.symm, open_tt_rec, reduceIte]
  case arrow l r ih_l ih_r => 
    simp only [open_tt_rec, arrow.injEq] at *
    have ⟨Hl, Hr⟩ := H 
    exact ⟨ih_l j V i U neq Hl, ih_r j V i U neq Hr⟩
  case all l r ih_l ih_r =>
    simp only [open_tt_rec, all.injEq] at *
    have ⟨Hl, Hr⟩ := H 
    refine ⟨ih_l j V i U neq Hl, ih_r (j + 1) V (i + 1) U (by grind) Hr⟩
  case sum l r ih_l ih_r => 
    simp only [open_tt_rec, sum.injEq] at *
    have ⟨Hl, Hr⟩ := H 
    exact ⟨ih_l j V i U neq Hl, ih_r j V i U neq Hr⟩
  case top => simp only [open_tt_rec]
  case fvar => simp only [open_tt_rec]

end LambdaCalculus.LocallyNameless.Fsub
