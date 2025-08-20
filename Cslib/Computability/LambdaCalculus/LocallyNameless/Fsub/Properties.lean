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

open Ty Term

omit [HasFresh Var] [DecidableEq Var] in
/-- An opening appearing in both sides of an equality of types can be removed. -/
@[scoped grind]
lemma Ty.openRec_lc_aux (T : Ty Var) j V i U (neq : i ≠ j) (h : T⟦j ↝ V⟧ᵞ = T⟦j ↝ V⟧ᵞ⟦i ↝ U⟧ᵞ) : 
    T = T⟦i ↝ U⟧ᵞ := by induction T generalizing j i <;> grind

/-- A locally closed type is unchanged by opening. -/
@[scoped grind =_]
lemma Ty.openRec_lc (T : Ty Var) U k (lc : T.LC) : T = T⟦k ↝ U⟧ᵞ := by
  induction lc generalizing k
  case all => 
    -- TODO: how to tell grind to try `free_union`?
    let ⟨x, _⟩ := fresh_exists <| free_union Var
    grind
  all_goals grind

omit [HasFresh Var] in
/-- Substitution of a free variable not present in a type leaves it unchanged. -/
@[scoped grind]
lemma Ty.subst_fresh (Z : Var) (U T : Ty Var) (nmem : Z ∉ T.fv) : T = T[Z := U] := by
  induction T <;> grind

/-- Substitution of a locally closed type distributes with opening. -/
@[scoped grind]
lemma Ty.subst_openRec (T1 T2 : Ty Var) (X : Var) (P : Ty Var) k (lc : P.LC) : 
    (T1⟦k ↝ T2⟧ᵞ)[X := P] = T1[X := P]⟦k ↝ T2[X := P]⟧ᵞ := by
  induction T1 generalizing k <;> grind

/-- Specialize `Ty.subst_openRec` to the first opening. -/
lemma Ty.subst_open (T1 T2 : Ty Var) (X : Var) (P : Ty Var) (lc : P.LC) :
    (T1 ^ᵞ T2)[X := P] = T1[X := P] ^ᵞ T2[X := P] := subst_openRec _ _ _ _ _ lc

/-- Specialize `Ty.subst_open` to free variables. -/
lemma Ty.subst_open_var (X Y : Var) (P T : Ty Var) (neq : Y ≠ X) (lc : P.LC) :
    (T ^ᵞ fvar Y)[X := P] = (T[X := P]) ^ᵞ fvar Y := by grind

omit [HasFresh Var] in
/-- Opening to a type is equivalent to opening to a free variable and substituting. -/
@[scoped grind]
lemma Ty.openRec_subst_intro (X : Var) (T2 U : Ty Var) (k : ℕ) (nmem : X ∉ T2.fv) :
    T2⟦k ↝ U⟧ᵞ = (T2⟦k ↝ fvar X⟧ᵞ)[X := U] := by
  induction T2 generalizing U k <;> grind

omit [HasFresh Var] in
/-- Specialize `Ty.openRec_subst_intro` to the first opening. -/
lemma Ty.open_subst_intro (X : Var) (T2 U : Ty Var) (nmem : X ∉ T2.fv) :
    T2 ^ᵞ U = (T2 ^ᵞ fvar X)[X := U] := openRec_subst_intro _ _ _ _ nmem

omit [HasFresh Var] [DecidableEq Var] in
@[scoped grind]
lemma Term.openRec_ty_lc_aux₁ (e : Term Var) j (u : Term Var) i (P : Ty Var) 
    (eq : e⟦j ↝ u⟧ᵗᵗ = e⟦j ↝ u⟧ᵗᵗ⟦i ↝ P⟧ᵗᵞ) : e = e⟦i ↝ P⟧ᵗᵞ
  := by induction e generalizing j i <;> grind

omit [HasFresh Var] [DecidableEq Var] in
@[scoped grind]
lemma Term.openRec_ty_lc_aux₂ (e : Term Var) j (Q : Ty Var) i (P : Ty Var) : 
    i ≠ j → e⟦j ↝ Q⟧ᵗᵞ = e⟦j ↝ Q⟧ᵗᵞ⟦i ↝ P⟧ᵗᵞ → e = e⟦i ↝ P⟧ᵗᵞ := by
  induction e generalizing j i <;> grind

/-- An opening (term to type) appearing in both sides of an equality of terms can be removed. -/
lemma Term.openRec_ty_lc (e : Term Var) (U : Ty Var) k (e_lc : e.LC) : e = e⟦k ↝ U⟧ᵗᵞ := by
  induction e generalizing k
  case abs T t ih =>
    simp [openRec_ty]
    refine ⟨by grind, ?_⟩
    cases e_lc with | abs L T_lc cofin =>
    have ⟨x, free⟩ := fresh_exists L
    ----rw [←openRec_ty_lc_aux₁ (j := 0) (u := fvar x)]
    ----rw [←openRec_ty_lc_aux₂ (j := 0) (Q := fvar x)]
    sorry    
  case tabs => sorry
  case let' => sorry
  case case => sorry
  all_goals grind

omit [HasFresh Var] in
/-- Substitution of a free type variable not present in a term leaves it unchanged. -/
lemma Term.subst_ty_fresh (X : Var) (U : Ty Var) (e : Term Var) (nmem : X ∉ e.fv_ty) : 
    e = e [X := U] := by induction e <;> grind

/-- Substitution of a locally closed type distributes with term opening to a type . -/
@[scoped grind]
lemma Term.subst_openRec_ty (e : Term Var) T (X : Var) (U : Ty Var) k (U_lc : U.LC) : 
    (e⟦k ↝ T⟧ᵗᵞ)[X := U] = (e[X := U])⟦k ↝  T[X := U]⟧ᵗᵞ := by
  induction e generalizing k <;> grind

/-- Specialize `Term.subst_openRec_ty` to the first opening. -/
lemma Term.subst_open_ty (e : Term Var) T (X : Var) (U : Ty Var) (U_lc : U.LC) : 
    (e ^ᵗᵞ T)[X := U] = e[X := U] ^ᵗᵞ T[X := U] := subst_openRec_ty e T X U 0 U_lc

/-- Specialize `Term.subst_open_ty` to free variables. -/
lemma Term.subst_open_var_ty (X Y : Var) (U : Ty Var) (e : Term Var) (neq : X ≠ Y) (U_lc : U.LC) :
    (e ^ᵗᵞ Ty.fvar Y)[X := U] = e[X := U] ^ᵗᵞ Ty.fvar Y := by grind

omit [HasFresh Var]
/-- Opening to a term to a type is equivalent to opening to a free variable and substituting. -/
lemma Term.openRec_subst_intro_ty (X : Var) (e : Term Var) (U : Ty Var) k (nmem : X ∉ e.fv_ty) : 
    e⟦k ↝ U⟧ᵗᵞ = (e⟦k ↝ Ty.fvar X⟧ᵗᵞ)[X := U] := by
  induction e generalizing X U k <;> grind

/-- Specialize `Term.openRec_subst_intro_ty` to the first opening. -/
lemma Term.open_subst_intro_ty (X : Var) (e : Term Var) (U : Ty Var) (nmem : X ∉ e.fv_ty) : 
    e ^ᵗᵞ U = (e ^ᵗᵞ Ty.fvar X)[X := U] := openRec_subst_intro_ty X e U 0 nmem

end LambdaCalculus.LocallyNameless.Fsub
