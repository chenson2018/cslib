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

namespace Term

omit [HasFresh Var] [DecidableEq Var] in
@[scoped grind]
lemma openRec_ty_lc_aux₁ (e : Term Var) j (u : Term Var) i (P : Ty Var) 
    (eq : e⟦j ↝ u⟧ᵗᵗ = e⟦j ↝ u⟧ᵗᵗ⟦i ↝ P⟧ᵗᵞ) : e = e⟦i ↝ P⟧ᵗᵞ
  := by induction e generalizing j i <;> grind

omit [HasFresh Var] [DecidableEq Var] in
@[scoped grind]
lemma openRec_ty_lc_aux₂ (e : Term Var) j (Q : Ty Var) i (P : Ty Var) : 
    i ≠ j → e⟦j ↝ Q⟧ᵗᵞ = e⟦j ↝ Q⟧ᵗᵞ⟦i ↝ P⟧ᵗᵞ → e = e⟦i ↝ P⟧ᵗᵞ := by
  induction e generalizing j i <;> grind

/-- An opening (term to type) appearing in both sides of an equality of terms can be removed. -/
@[scoped grind]
lemma openRec_ty_lc (e : Term Var) (U : Ty Var) k (e_lc : e.LC) : e = e⟦k ↝ U⟧ᵗᵞ := by
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
lemma subst_ty_fresh (X : Var) (U : Ty Var) (e : Term Var) (nmem : X ∉ e.fv_ty) : 
    e = e [X := U] := by induction e <;> grind

/-- Substitution of a locally closed type distributes with term opening to a type . -/
@[scoped grind]
lemma subst_openRec_ty (e : Term Var) T (X : Var) (U : Ty Var) k (U_lc : U.LC) : 
    (e⟦k ↝ T⟧ᵗᵞ)[X := U] = (e[X := U])⟦k ↝  T[X := U]⟧ᵗᵞ := by
  induction e generalizing k <;> grind

/-- Specialize `subst_openRec_ty` to the first opening. -/
lemma subst_open_ty (e : Term Var) T (X : Var) (U : Ty Var) (U_lc : U.LC) : 
    (e ^ᵗᵞ T)[X := U] = e[X := U] ^ᵗᵞ T[X := U] := subst_openRec_ty e T X U 0 U_lc

/-- Specialize `subst_open_ty` to free variables. -/
lemma subst_open_var_ty (X Y : Var) (U : Ty Var) (e : Term Var) (neq : X ≠ Y) (U_lc : U.LC) :
    (e ^ᵗᵞ Ty.fvar Y)[X := U] = e[X := U] ^ᵗᵞ Ty.fvar Y := by grind

omit [HasFresh Var]
/-- Opening to a term to a type is equivalent to opening to a free variable and substituting. -/
lemma openRec_subst_intro_ty (X : Var) (e : Term Var) (U : Ty Var) k (nmem : X ∉ e.fv_ty) : 
    e⟦k ↝ U⟧ᵗᵞ = (e⟦k ↝ Ty.fvar X⟧ᵗᵞ)[X := U] := by
  induction e generalizing X U k <;> grind

/-- Specialize `openRec_subst_intro_ty` to the first opening. -/
lemma open_subst_intro_ty (X : Var) (e : Term Var) (U : Ty Var) (nmem : X ∉ e.fv_ty) : 
    e ^ᵗᵞ U = (e ^ᵗᵞ Ty.fvar X)[X := U] := openRec_subst_intro_ty X e U 0 nmem

omit [DecidableEq Var] in
@[scoped grind]
lemma openRec_tm_lc_aux₁ (e : Term Var) j v u i (neq : i ≠ j)
    (eq : e⟦j ↝ v⟧ᵗᵗ = e⟦j ↝ v⟧ᵗᵗ⟦i ↝ u⟧ᵗᵗ) : e = e⟦i ↝ u⟧ᵗᵗ := by
  induction e generalizing i j <;> grind

omit [DecidableEq Var] in
@[scoped grind]
lemma openRec_tm_lc_aux₂ (e : Term Var) j V u i (eq : e⟦j ↝ V⟧ᵗᵞ = e⟦j ↝ V⟧ᵗᵞ⟦i ↝ u⟧ᵗᵗ) :
    e = e⟦i ↝ u⟧ᵗᵗ := by
  induction e generalizing i j <;> grind

/-- An opening (term to term) appearing in both sides of an equality of terms can be removed. -/
@[scoped grind]
lemma openRec_tm_lc (u e : Term Var) k (e_lc : e.LC) : e = e⟦k ↝ u⟧ᵗᵗ := by
  induction e_lc generalizing k
  case abs => sorry
  case tabs => sorry
  case let' => sorry
  case case => sorry
  all_goals grind

/-- Substitution of a term variable not present in a term leaves it unchanged. -/
lemma subst_tm_fresh x (u e : Term Var) (nmem : x ∉ e.fv_tm) : e = e[x := u] := by
  induction e <;> grind

/-- Term substitution distributes with term opening . -/
lemma subst_tm_openRec_tm (e1 e2 : Term Var) (x : Var) (u : Term Var) k (u_lc : u.LC) :
    (e1⟦k ↝ e2⟧ᵗᵗ)[x := u] = (e1[x := u])⟦k ↝  e2[x := u]⟧ᵗᵗ := by
  induction e1 generalizing k <;> grind

/-- Specialize `subst_openRec_tm` to the first opening. -/
lemma subst_tm_open_tm (e1 e2 : Term Var) (x : Var) (u : Term Var) (u_lc : u.LC) :
    (e1 ^ᵗᵗ e2)[x := u] = (e1[x := u]) ^ᵗᵗ e2[x := u] := subst_tm_openRec_tm e1 e2 x u 0 u_lc

/-- Specialize `subst_open_tm` to free variables. -/
lemma subst_tm_open_var_tm (e : Term Var) (x y : Var) (u : Term Var) (neq : y ≠ x) (u_lc : u.LC) :
    (e ^ᵗᵗ fvar y)[x := u] = (e[x := u]) ^ᵗᵗ fvar y := by grind [subst_tm_open_tm]

/-- Type substitution distributes with term opening . -/
lemma subst_ty_openRec_tm (e1 e2 : Term Var) (Z : Var) (P : Ty Var) k : 
    (e1⟦k ↝ e2⟧ᵗᵗ)[Z := P] = (e1[Z := P])⟦k ↝ e2[Z := P]⟧ᵗᵗ := sorry

/-- Specialize `subst_ty_openRec_tm` to the first opening. -/
lemma subst_ty_open_tm (e1 e2 : Term Var) (Z : Var) (P : Ty Var) : 
    (e1 ^ᵗᵗ e2)[Z := P] = (e1[Z := P]) ^ᵗᵗ e2[Z := P] := subst_ty_openRec_tm e1 e2 Z P 0

/-- Specialize `subst_ty_openRec_tm` to the first opening. -/
lemma subst_ty_open_var_tm (e : Term Var) (Z x : Var) (P : Ty Var) : 
    (e ^ᵗᵗ fvar x)[Z := P] = (e[Z := P]) ^ᵗᵗ fvar x := by grind [subst_ty_open_tm]

lemma subst_tm_openRec_ty (e : Term Var) (P : Ty Var) (z : Var) (u : Term Var) k (u_lc : u.LC) :
    (e⟦k ↝ P⟧ᵗᵞ)[z := u] = e[z := u]⟦k ↝ P⟧ᵗᵞ := sorry

lemma subst_tm_open_ty (e : Term Var) (P : Ty Var) (z : Var) (u : Term Var) (u_lc : u.LC) :
    (e ^ᵗᵞ P)[z := u] = e[z := u] ^ᵗᵞ P := by apply subst_tm_openRec_ty (k := 0) (u_lc := u_lc)

lemma subst_tm_open_var_ty (e : Term Var) (z X : Var) (u : Term Var) (u_lc : u.LC) :
    (e ^ᵗᵞ Ty.fvar X)[z := u] = e[z := u] ^ᵗᵞ Ty.fvar X := subst_tm_open_ty _ _ _ _ u_lc

lemma openRec_subst_intro_tm (x : Var) (e u : Term Var) k (nmem : x ∉ e.fv_tm) :
    e⟦k ↝ u⟧ᵗᵗ = (e⟦k ↝ fvar x⟧ᵗᵗ)[x := u] := by
  induction e generalizing k <;> grind

lemma open_subst_intro_tm (x : Var) (e u : Term Var) (nmem : x ∉ e.fv_tm) :
    e ^ᵗᵗ u = (e ^ᵗᵗ fvar x)[x := u] := openRec_subst_intro_tm x e u 0 nmem

end Term

@[scoped grind =>]
lemma Ty.subst_lc (Z : Var) (P T : Ty Var) (T_lc : T.LC) (P_lc : P.LC) : T[Z := P].LC := by
  induction T_lc
  case all => apply LC.all (free_union Var) <;> grind
  -- TODO : make these forward rules?
  all_goals grind [LC.top, LC.var, LC.arrow, LC.sum]
    
lemma Term.subst_ty_lc (Z : Var) (P : Ty Var) (e : Term Var) (e_lc : e.LC) (P_lc : P.LC) :
    e[Z := P].LC := by
  induction e_lc
  case abs => sorry
  case tabs => sorry
  case let' => sorry
  case case => sorry
  -- TODO : make these forward rules?
  all_goals grind [LC.var, LC.app, LC.inl, LC.inr, LC.tapp]

lemma Term.subst_tm_lc (z : Var) (e1 e2 : Term Var) (e1_lc : e1.LC) (e2_lc : e2.LC) :
    e1[z := e2].LC := sorry

end LambdaCalculus.LocallyNameless.Fsub
