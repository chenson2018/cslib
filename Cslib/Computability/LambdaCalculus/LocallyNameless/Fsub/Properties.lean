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

omit [HasFresh Var] [DecidableEq Var] in
 /-- An opening appearing in both sides of an equality of terms can be removed. -/
@[grind]
lemma Ty.open_lc_aux (T : Ty Var) j V i U (neq : i ≠ j) (h : T⟦j ↝ V⟧ = (T⟦j ↝ V⟧)⟦i ↝ U⟧) : 
    T = T⟦i ↝ U⟧ := by induction T generalizing j i <;> grind

@[grind]
lemma Ty.open_lc (T : Ty Var) U k (lc : T.LC) : T = T⟦k ↝ U⟧ := by
  induction lc generalizing k
  case all => 
    -- TODO: how to tell grind to try `free_union`?
    let ⟨x, _⟩ := fresh_exists <| free_union Var
    grind
  all_goals grind

omit [HasFresh Var] in
/-- Substitution of a free variable not present in a type leaves it unchanged. -/
lemma Ty.subst_fresh (Z : Var) (U T : Ty Var) (nmem : Z ∉ T.fv) : T = T[Z := U] := by
  induction T <;> grind

/-- Substitution of a locally closed type distributes with opening. -/
lemma Ty.subst_openRec (T1 T2 : Ty Var) (X : Var) (P : Ty Var) k (lc : P.LC) : 
    (T1⟦k ↝ T2⟧)[X := P] = (T1[X := P])⟦k ↝ T2[X := P]⟧ := by
  induction T1 generalizing k <;> grind

/-- Specialize `Ty.subst_openRec` to the first opening. -/
lemma Ty.subst_open (T1 T2 : Ty Var) (X : Var) (P : Ty Var) (lc : P.LC) :
    (T1 ^ T2)[X := P] = T1[X := P] ^ T2[X := P] := subst_openRec _ _ _ _ _ lc

/-- Specialize `Ty.subst_open` to free variables. -/
lemma Ty.subst_open_var (X Y : Var) (P T : Ty Var) (neq : Y ≠ X) (lc : P.LC) :
    (T[X := P]) ^ fvar Y = (T ^ fvar Y)[X := P] := by
  have := Ty.subst_open T (fvar Y) X P lc
  grind

omit [HasFresh Var] in
/-- Opening to a type is equivalent to opening to a free variable and substituting. -/
lemma Ty.openRec_subst_intro (X : Var) (T2 U : Ty Var) (k : ℕ) (nmem : X ∉ T2.fv) :
    T2⟦k ↝ U⟧ = (T2⟦k ↝ fvar X⟧)[X := U] := by
  induction T2 generalizing U k <;> grind

omit [HasFresh Var] in
/-- Specialize `Ty.openRec_subst_intro` to the first opening. -/
lemma Ty.open_subst_intro (X : Var) (T2 U : Ty Var) (nmem : X ∉ T2.fv) :
    T2 ^ U = (T2 ^ fvar X)[X := U] := by
  apply openRec_subst_intro
  grind

end LambdaCalculus.LocallyNameless.Fsub
