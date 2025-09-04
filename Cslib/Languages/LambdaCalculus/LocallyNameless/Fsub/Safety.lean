/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing
import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Reduction

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file proves type safety.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

variable {Γ Δ Θ : Env Var} {σ τ δ : Ty Var}

namespace Ty.Sub

open Ty.Wf Env.Wf Context List

omit [HasFresh Var] in
@[grind <=]
lemma refl (wf_Γ : Γ.Wf) (wf_σ : σ.Wf Γ) : Sub Γ σ σ := by
  induction wf_σ with
  | all => apply all (free_union [Context.dom] Var) <;> grind
  | _ => grind

lemma weaken (sub : Sub (Γ ++ Θ) σ σ') (wf : (Γ ++ Δ ++ Θ).Wf) : Sub (Γ ++ Δ ++ Θ) σ σ' := by
  generalize eq : Γ ++ Θ = ΓΘ at sub
  induction sub generalizing Γ 
  case trans_tvar σ _ _ X mem _ _=> 
    have : (Γ ++ Δ ++ Θ).Perm (Δ ++ Γ ++ Θ) := by grind [perm_append_comm_assoc]
    have : X ∉ Δ.keys := by grind [mem_keys_append_NodupKeys]
    grind [dlookup_append, dlookup_eq_none]
  case all σ _ _ _ _ _ _ _ ih => 
    subst eq
    apply all (free_union [Context.dom] Var)
    · grind
    · intro X mem
      have wf : Env.Wf ((⟨X, Binding.sub σ⟩ :: Γ) ++ Δ ++ Θ) := sorry
      specialize ih X (by grind) wf (by grind)
      grind
  all_goals grind  

@[simp, grind]
def TransOn (δ : Ty Var) := ∀ Γ σ τ, Sub Γ σ δ → Sub Γ δ τ → Sub Γ σ τ 

-- TODO: make the params of this match up with `narrow`, or maybe even inline it?
lemma narrow_aux (trans : TransOn δ) (sub₁ : Sub (Γ ++ [⟨X, Binding.sub δ⟩] ++ Δ) σ τ)
    (sub₂ : Sub Δ δ' δ) : Sub (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) σ τ := sorry

lemma trans (Γ : Env Var) : Transitive (Sub Γ) := sorry

lemma narrow (sub_δ : Sub Δ δ δ') (sub_narrow : Sub (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) σ τ) :
    Sub (Γ ++ [⟨X, Binding.sub δ⟩] ++ Δ) σ τ := by
  apply narrow_aux (δ := δ')
  · intros Γ _ _ s1 s2
    exact trans Γ s1 s2 -- TODO: grind this..., Transitive → TransOn
  · exact sub_narrow
  · exact sub_δ

lemma map_subst (sub₁ : Sub (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) σ τ) (sub₂ : Sub Δ δ δ') :
    Sub (Γ.map_val (·[X:=δ]) ++ Δ) (σ[X:=δ]) (τ[X:=δ]) := sorry

end Ty.Sub

end LambdaCalculus.LocallyNameless.Fsub
