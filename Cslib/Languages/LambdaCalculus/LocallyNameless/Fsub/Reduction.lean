/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Opening

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines a call-by-value reduction.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u}

namespace LambdaCalculus.LocallyNameless.Fsub

namespace Term

/-- Existential predicate for being a locally closed body of an abstraction. -/
@[scoped grind =]
def body (t : Term Var) := ∃ L : Finset Var, ∀ x ∉ L, LC (t ^ᵗᵗ fvar x)

/-- Values are irreducible terms. -/
inductive Value : Term Var → Prop
  | abs : LC (abs σ t₁) → Value (abs σ t₁)
  | tabs : LC (tabs σ t₁) → Value (tabs σ t₁)
  | inl : Value t₁ → Value (inl t₁)
  | inr : Value t₁ → Value (inr t₁)

lemma Value.lc {t : Term Var} (val : t.Value) : t.LC := by
  induction val <;> grind

/-- The call-by-value reduction relation. -/
inductive Red : Term Var → Term Var → Prop
  | appₗ : LC t₂ → Red t₁ t₁' → Red (app t₁ t₂) (app t₁' t₂)
  | appᵣ : Value t₁ → Red t₂ t₂' → Red (app t₁ t₂) (app t₁ t₂')
  | tapp : σ.LC → Red t₁ t₁' → Red (tapp t₁ σ) (tapp t₁' σ)
  | abs : LC (abs T t₁) → Value t₂ → Red (app (abs T t₁) t₂) (t₁ ^ᵗᵗ t₂)
  | tabs : LC (tabs T1 t₁) → T2.LC → Red (tapp (tabs T1 t₁) T2) (t₁ ^ᵗᵞ T2)
  | let_bind : Red t₁ t₁' → t₂.body → Red (let' t₁ t₂) (let' t₁' t₂)
  | let_body : Value t₁ → t₂.body → Red (let' t₁ t₂) (t₂ ^ᵗᵗ t₁)
  | inl : Red t₁ t₁' → Red (inl t₁) (inl t₁')
  | inr : Red t₁ t₁' → Red (inr t₁) (inr t₁')
  | case : Red t₁ t₁' → t₂.body → t₃.body → Red (case t₁ t₂ t₃) (case t₁' t₂ t₃)
  | case_inl : Value t₁ → t₂.body → t₃.body → Red (case (inl t₁) t₂ t₃) (t₂ ^ᵗᵗ t₁)
  | case_inr : Value t₁ → t₂.body → t₃.body → Red (case (inr t₁) t₂ t₃) (t₃ ^ᵗᵗ t₁)

lemma Red.lc {t t' : Term Var} (red : Red t t') : t.LC ∧ t'.LC :=
  sorry

end Term

end LambdaCalculus.LocallyNameless.Fsub
