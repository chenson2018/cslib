/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.WellFormed

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the typing and subtyping relations.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

namespace LambdaCalculus.LocallyNameless.Fsub

namespace Ty

/-- The subtyping relation. -/
inductive Sub : Env Var → Ty Var → Ty Var → Prop
  | top : Γ.Wf → σ.Wf Γ → Sub Γ σ top
  | refl_tvar : Γ.Wf → (fvar X).Wf Γ → Sub Γ (fvar X) (fvar X)
  | trans_tvar : Binding.sub σ ∈ Γ.dlookup X → Sub Γ σ σ' → Sub Γ (fvar X) σ'
  | arrow : Sub Γ σ σ' → Sub Γ τ' τ → Sub Γ (arrow σ' τ') (arrow σ τ)
  | all (L : Finset Var) :
      Sub Γ σ σ' →
      (∀ X ∉ L, Sub (⟨X, Binding.sub σ⟩ :: Γ) (τ' ^ᵞ fvar X) (τ ^ᵞ fvar X)) →
      Sub Γ (all σ' τ') (all σ τ)
  | sum : Sub Γ σ' σ → Sub Γ τ' τ → Sub Γ (sum σ' τ') (sum σ τ)

lemma Sub.lc (Γ : Env Var) (σ τ : Ty Var) (sub : Sub Γ σ τ) : Γ.Wf ∧ σ.Wf Γ ∧ τ.Wf Γ := 
  sorry

end Ty

open Term Ty in
/-- The typing relation. -/
inductive Typing : Env Var → Term Var → Ty Var → Prop
  | var : Γ.Wf → Binding.ty σ ∈ Γ.dlookup x → Typing Γ (fvar x) σ
  | abs (L : Finset Var) :
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₁ ^ᵗᵗ fvar x) τ) →
      Typing Γ (abs σ t₁) (arrow σ τ)
  | app : Typing Γ t₁ (arrow σ τ) → Typing Γ t₂ σ → Typing Γ (app t₁ t₂) τ
  | tabs (L : Finset Var) :
      (∀ X ∉ L, Typing (⟨X, Binding.sub σ⟩ :: Γ) (t₁ ^ᵗᵞ fvar X) (τ ^ᵞ fvar X)) →
      Typing Γ (tabs σ t₁) (all σ τ)
  | tapp : Typing Γ t₁ (all σ τ) → Sub Γ σ' σ → Typing Γ (tapp t₁ σ') (τ ^ᵞ σ')
  | sub : Typing Γ t τ → Sub Γ τ τ' → Typing Γ t τ'
  | let' (L : Finset Var) :
      Typing Γ t₁ σ →
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ fvar x) τ) →
      Typing Γ (let' t₁ t₂) τ
  | inl : Typing Γ t₁ σ → τ.Wf Γ → Typing Γ (inl t₁) (sum σ τ)
  | inr : Typing Γ t₁ τ → σ.Wf Γ → Typing Γ (inr t₁) (sum σ τ)
  | case (L : Finset Var) :
      Typing Γ t₁ (sum σ τ) →
      (∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ fvar x) δ) →
      (∀ x ∉ L, Typing (⟨x, Binding.ty τ⟩ :: Γ) (t₃ ^ᵗᵗ fvar x) δ) →
      Typing Γ (case t₁ t₂ t₃) δ

lemma Typing.lc (Γ : Env Var) (t : Term Var) (τ : Ty Var) (der : Typing Γ t τ) :
    Γ.Wf ∧ t.LC ∧ τ.Wf Γ := sorry

end LambdaCalculus.LocallyNameless.Fsub
