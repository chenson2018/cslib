/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic


/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines opening and local closure.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Fsub

namespace Ty

/-- Variable opening (type opening to type) of the ith bound variable. -/
@[scoped grind =]
def openRec (X : ℕ) (δ : Ty Var) : Ty Var → Ty Var
| top => top
| bvar Y => if X = Y then δ else bvar Y
| fvar X => fvar X
| arrow σ τ => arrow (openRec X δ σ) (openRec X δ τ)
| all σ τ => all (openRec X δ σ) (openRec (X + 1) δ τ)
| sum σ τ => sum (openRec X δ σ) (openRec X δ τ)

scoped notation:68 γ "⟦" X " ↝ " δ "⟧ᵞ"=> openRec X δ γ

/-- An opening appearing in both sides of an equality of types can be removed. -/
@[scoped grind]
lemma openRec_neq_eq {σ τ γ : Ty Var} (neq : X ≠ Y) (h : σ⟦Y ↝ τ⟧ᵞ = σ⟦Y ↝ τ⟧ᵞ⟦X ↝ γ⟧ᵞ) : 
    σ = σ⟦X ↝ γ⟧ᵞ := by induction σ generalizing Y X <;> grind

/-- Variable opening (type opening to type) of the closest binding. -/
@[scoped grind =]
def open' (γ δ : Ty Var) := openRec 0 δ γ

scoped infixr:80 " ^ᵞ " => open'

/-- Locally closed types. -/
@[scoped grind cases]
inductive LC : Ty Var → Prop
  | top : LC top
  | var : LC (fvar X)
  | arrow : LC σ → LC τ → LC (arrow σ τ)
  | all (L : Finset Var) : LC σ → (∀ X ∉ L, LC (τ ^ᵞ fvar X)) → LC (all σ τ)
  | sum : LC σ → LC τ → LC (sum σ τ)

variable [HasFresh Var] [DecidableEq Var]

/-- A locally closed type is unchanged by opening. -/
@[scoped grind =_]
lemma openRec_lc {σ τ : Ty Var} (lc : σ.LC) : σ = σ⟦X ↝ τ⟧ᵞ := by
  induction lc generalizing X <;> (have := fresh_exists <| free_union Var; grind)

end Ty

namespace Term

open scoped Ty

/-- Variable opening (term opening to type) of the ith bound variable. -/
@[scoped grind =]
def openRec_ty (X : ℕ) (δ : Ty Var) : Term Var → Term Var
| bvar x => bvar x
| fvar x => fvar x
| abs σ t₁ => abs (σ⟦X ↝ δ⟧ᵞ) (openRec_ty X δ t₁)
| app t₁ t₂ => app (openRec_ty X δ t₁) (openRec_ty X δ t₂)
| tabs σ t₁ => tabs (σ⟦X ↝ δ⟧ᵞ) (openRec_ty (X + 1) δ t₁)
| tapp t₁ σ => tapp (openRec_ty X δ t₁) (σ⟦X ↝ δ⟧ᵞ)
| let' t₁ t₂ => let' (openRec_ty X δ t₁) (openRec_ty X δ t₂)
| inl t₁ => inl (openRec_ty X δ t₁)
| inr t₂ => inr (openRec_ty X δ t₂)
| case t₁ t₂ t₃ => case (openRec_ty X δ t₁) (openRec_ty X δ t₂) (openRec_ty X δ t₃)

scoped notation:68 t "⟦" X " ↝ " δ "⟧ᵗᵞ"=> openRec_ty X δ t

/-- An opening (term to type) appearing in both sides of an equality of terms can be removed. -/
@[scoped grind]
lemma openRec_ty_neq_eq (neq : X ≠ Y) (eq : t⟦Y ↝ σ⟧ᵗᵞ = t⟦Y ↝ σ⟧ᵗᵞ⟦X ↝ τ⟧ᵗᵞ) : 
    t = t⟦X ↝ τ⟧ᵗᵞ := by
  induction t generalizing X Y <;> grind

/-- Variable opening (term opening to type) of the closest binding. -/
@[scoped grind =]
def open_ty (t : Term Var) (δ : Ty Var) := openRec_ty 0 δ t

scoped infixr:80 " ^ᵗᵞ " => open_ty

/-- Variable opening (term opening to term) of the ith bound variable. -/
@[scoped grind =]
def openRec_tm (x : ℕ) (s : Term Var) : Term Var → Term Var
| bvar y => if x = y then s else (bvar y)
| fvar x => fvar x
| abs σ t₁ => abs σ (openRec_tm (x + 1) s t₁)
| app t₁ t₂ => app (openRec_tm x s t₁) (openRec_tm x s t₂)
| tabs σ t₁ => tabs σ (openRec_tm x s t₁)
| tapp t₁ σ => tapp (openRec_tm x s t₁) σ
| let' t₁ t₂ => let' (openRec_tm x s t₁) (openRec_tm (x + 1) s t₂)
| inl t₁ => inl (openRec_tm x s t₁)
| inr t₂ => inr (openRec_tm x s t₂)
| case t₁ t₂ t₃ => case (openRec_tm x s t₁) (openRec_tm (x + 1) s t₂) (openRec_tm (x + 1) s t₃)

scoped notation:68 t "⟦" x " ↝ " s "⟧ᵗᵗ"=> openRec_tm x s t

/-- An opening (term to term) appearing in both sides of an equality of terms can be removed. -/
@[scoped grind]
lemma openRec_tm_neq_eq (neq : x ≠ y) (eq : t⟦y ↝ s₁⟧ᵗᵗ = t⟦y ↝ s₁⟧ᵗᵗ⟦x ↝ s₂⟧ᵗᵗ) : 
    t = t⟦x ↝ s₂⟧ᵗᵗ := by
  induction t generalizing x y <;> grind

/-- Variable opening (term opening to term) of the closest binding. -/
@[scoped grind =]
def open_tm (t₁ t₂ : Term Var) := openRec_tm 0 t₂ t₁

scoped infixr:80 " ^ᵗᵗ " => open_tm

/-- Locally closed terms. -/
@[scoped grind cases]
inductive LC : Term Var → Prop
  | var : LC (fvar x)
  | abs (L : Finset Var) : σ.LC → (∀ x ∉ L, LC (t₁ ^ᵗᵗ fvar x)) → LC (abs σ t₁)
  | app : LC t₁ → LC t₂ → LC (app t₁ t₂)
  | tabs (L : Finset Var) : σ.LC → (∀ X ∉ L, LC (t₁ ^ᵗᵞ .fvar X)) → LC (tabs σ t₁)
  | tapp : LC t₁ → σ.LC → LC (tapp t₁ σ)
  | let' (L : Finset Var) : LC t₁ → (∀ x ∉ L, LC (t₂ ^ᵗᵗ fvar x)) → LC (let' t₁ t₂)
  | inl : LC t₁ → LC (inl t₁)
  | inr : LC t₁ → LC (inr t₁)
  | case (L : Finset Var) :
      LC t₁ →
      (∀ x ∉ L, LC (t₂ ^ᵗᵗ fvar x)) →
      (∀ x ∉ L, LC (t₃ ^ᵗᵗ fvar x)) →
      LC (case t₁ t₂ t₃)

variable {t s : Term Var} {x y X Y : ℕ} {σ δ : Ty Var}

/-- Elimination of mixed term and type opening. -/
@[scoped grind]
lemma openRec_tm_ty_eq (eq : t⟦x ↝ s⟧ᵗᵗ = t⟦x ↝ s⟧ᵗᵗ⟦y ↝ δ⟧ᵗᵞ) : t = t⟦y ↝ δ⟧ᵗᵞ
  := by induction t generalizing x y <;> grind

/-- Elimination of mixed term and type opening. -/
@[scoped grind]
lemma openRec_ty_tm_eq (eq : t⟦Y ↝ σ⟧ᵗᵞ = t⟦Y ↝ σ⟧ᵗᵞ⟦x ↝ s⟧ᵗᵗ) : t = t⟦x ↝ s⟧ᵗᵗ := by
  induction t generalizing x Y <;> grind

variable [HasFresh Var] [DecidableEq Var]

/-- A locally closed term is unchanged by type opening. -/
@[scoped grind]
lemma openRec_ty_lc {t : Term Var} (lc : t.LC) : t = t⟦X ↝ σ⟧ᵗᵞ := by
  induction t generalizing X
  case abs | tabs | let' | case => sorry
  all_goals grind

/-- A locally closed term is unchanged by term opening. -/
@[scoped grind]
lemma openRec_tm_lc (lc : t.LC) : t = t⟦x ↝ s⟧ᵗᵗ := by
  induction t generalizing x
  case abs  | tabs | let' | case => sorry
  all_goals grind

end Term

end LambdaCalculus.LocallyNameless.Fsub
