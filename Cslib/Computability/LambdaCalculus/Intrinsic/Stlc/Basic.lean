/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Mathlib
import Cslib.Computability.LambdaCalculus.Intrinsic.Stlc.AesopRuleset
import Cslib.Syntax.HasSubstitution
import Mathlib.Logic.Relation

/-! # λ-calculus

The simply typed λ-calculus, with intrinsically typed derivations.

## References

* <https://plfa.github.io/>

-/

universe u v

variable {Var : Type u} {Base : Type v} [DecidableEq Var]

namespace LambdaCalculus.Intrinsic.Stlc

/-- Types of the simply typed lambda calculus. -/
inductive Ty (Base : Type v)
  /-- A base type, from a typing context. -/
  | base : Base → Ty Base
  /-- A function type. -/
  | arrow : Ty Base → Ty Base → Ty Base

scoped infixr:70 " ⤳ " => Ty.arrow

/-- A typing context. -/
abbrev Context (Base : Type v) := List (Ty Base)

@[aesop unsafe [constructors, cases]]
inductive Term : Context Base → Ty Base → Prop
  /-- A variable, from a context judgement. -/ 
  | var : a ∈ Γ → Term Γ a
  /-- Lambda abstraction. -/
  | abs : Term (a :: Γ) b → Term Γ (a ⤳ b)
  /-- Function application. -/
  | app : Term Γ (a ⤳ b) → Term Γ a → Term Γ b

scoped notation:50 Γ " ⊢ " τ:arg => Term Γ τ

variable {Γ Δ : Context Base}

namespace Term

theorem rename (ρ : Γ ⊆ Δ) {τ} (der : Γ ⊢ τ) : Δ ⊢ τ := by
  revert ρ Δ
  induction der <;> aesop

theorem exts (sig : ∀ {σ}, σ ∈ Γ → Δ ⊢ σ) : ∀ {σ τ}, τ ∈ σ :: Γ → σ :: Δ ⊢ τ  
  := by
  intros σ τ mem
  cases mem
  case head => aesop
  case tail mem => exact (sig mem).rename (by simp) 

theorem subst (sig : ∀ {σ}, σ ∈ Γ → Δ ⊢ σ) {σ} : Γ ⊢ σ → Δ ⊢ σ := by
  intros der
  revert sig Δ
  induction der <;> intros Δ sig
  case var => aesop
  case abs Γ σ τ _ ih => exact abs (ih (exts sig))
  case app σ τ _ _ _ _=> refine @app _ _ σ τ ?_ ?_ <;> simp_all

theorem subst_single (body : σ :: Γ ⊢ τ) (sub : Γ ⊢ σ) : Γ ⊢ τ := 
  subst (by aesop) body

notation t:max "[" t' "]" => Term.subst_single t t'

inductive Value : Γ ⊢ τ → Prop
| abs {N : τ :: Γ ⊢ σ} : Value N.abs

inductive CBV : Γ ⊢ τ → Γ ⊢ τ → Prop
  /-- Reduce an application to a lambda term. -/ 
  | beta : Value N → CBV (app (abs M) N) (M[N])
  /-- Left congruence rule for application. -/
  | appL : Value Z → CBV M N → CBV (app Z M) (app Z N)
  /-- Right congruence rule for application. -/
  | appR : CBV M N → CBV (app M Z) (app N Z)

notation t:39 " ⭢ᵥ " t':39 => CBV t t'
notation t:39 " ↠ᵥ " t':39 => (Relation.ReflTransGen CBV) t t'

inductive Progress (M : Γ ⊢ τ) : Prop
| step {N} : (M ⭢ᵥ N) → Progress M
| done : Value M → Progress M

set_option pp.proofs true in
theorem progress (M : [] ⊢ τ) : Progress M := by
  generalize eq : [] = Γ at M
  induction M
  case var mem =>
    subst eq
    simp at mem
  case app σ τ l r prog_l prog_r => 
    subst eq
    simp_all only [forall_const]
    cases prog_l
    case step l' step_l => 
      apply Progress.step
      apply CBV.appR step_l
      exact r
    case done val_l =>
      cases prog_r
      case step step_r => exact Progress.step (CBV.appL val_l step_r)
      case done val_r => 
        apply Progress.step
        apply CBV.beta val_r
        cases val_l
        assumption 
  case abs =>
    apply Progress.done
    constructor
    assumption

end LambdaCalculus.Intrinsic.Stlc.Term
