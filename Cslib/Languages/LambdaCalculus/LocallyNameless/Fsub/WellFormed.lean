/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Opening

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines the well-formedness condition for types and contexts.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open scoped Ty in
/-- A type is well-formed when it is locally closed and all free variables appear in a context. -/
inductive Ty.Wf : Env Var → Ty Var → Prop
  | top : Ty.Wf Γ top
  | var : Binding.sub σ ∈ Γ.dlookup X → Ty.Wf Γ (fvar X)
  | arrow : Ty.Wf Γ σ → Ty.Wf Γ τ → Ty.Wf Γ (arrow σ τ)
  | all (L : Finset Var) : 
      Ty.Wf Γ σ →
      (∀ X ∉ L, Ty.Wf (⟨X,Binding.sub σ⟩ :: Γ) (τ ^ᵞ fvar X)) →
      Ty.Wf Γ (all σ τ)
  | sum : Ty.Wf Γ σ → Ty.Wf Γ τ → Ty.Wf Γ (sum σ τ)

attribute [scoped grind] Ty.Wf.top Ty.Wf.var Ty.Wf.arrow Ty.Wf.sum

/-- An environment is well-formed if it binds each variable exactly once to a well-formed type. -/
inductive Env.Wf : Env Var → Prop
  | empty : Wf []
  | sub : Wf Γ → T.Wf Γ → X ∉ Γ.dom → Wf (⟨X, Binding.sub T⟩ :: Γ)
  | ty : Wf Γ → T.Wf Γ → x ∉ Γ.dom → Wf (⟨x, Binding.ty T⟩ :: Γ)

namespace Ty.Wf

open List

variable {Γ Δ Θ : Env Var} {σ τ τ' : Ty Var}

theorem perm_env (wf : σ.Wf Γ) (perm : Γ ~ Δ) (ok_Γ : Γ✓) (ok_Δ : Δ✓) : σ.Wf Δ := by
  induction wf generalizing Δ 
  case all σ τ _ _ _ _ ih => 
    apply all (free_union [Context.dom] Var) (by grind)
    intro X mem
    refine ih _ ?_ (Perm.cons _ perm) (nodupKeys_cons.mpr ?_) (nodupKeys_cons.mpr ?_)
    -- TODO: understand why we need simp here
    all_goals simp at mem; grind
  all_goals grind [perm_dlookup]

theorem lc (wf : σ.Wf Γ) : σ.LC := by
  induction wf
  -- TODO: how to get grind to do this???
  case all => apply LC.all (free_union Var) <;> grind
  all_goals grind

theorem weaken (wf_ΓΔ : σ.Wf (Γ ++ Δ)) (ok_ΓΔΘ : (Γ ++ Δ ++ Θ)✓) : σ.Wf (Γ ++ Δ ++ Θ) := by
  generalize eq : Γ ++ Δ = ΓΔ at wf_ΓΔ
  induction wf_ΓΔ generalizing Γ 
  case all σ _ _ _ _ _ ih =>
    apply all (free_union [Context.dom] Var) (by grind)
    intro X _
    -- TODO eliminate the simp
    apply ih (Γ := ⟨X, Binding.sub σ⟩ :: Γ) 
    <;> simp [Context.haswellformed_def, keys] at * 
    <;> grind
  case var => 
    observe : (Γ ++ Δ).Sublist (Γ ++ Δ ++ Θ)
    grind [NodupKeys.sublist]
  all_goals grind

theorem weaken_head (wf : σ.Wf Γ) (ok : (Γ ++ Δ)✓) : σ.Wf (Γ ++ Δ) := by
  have : Γ ++ Δ = [] ++ Γ ++ Δ := by rfl
  grind [weaken]  

variable [HasFresh Var]

end Ty.Wf

namespace Term

open scoped Ty

end Term

end LambdaCalculus.LocallyNameless.Fsub
