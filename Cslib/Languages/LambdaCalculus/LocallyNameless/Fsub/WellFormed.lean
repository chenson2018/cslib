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

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

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
@[grind]
inductive Env.Wf : Env Var → Prop
  | empty : Wf []
  | sub : Wf Γ → T.Wf Γ → X ∉ Γ.dom → Wf (⟨X, Binding.sub T⟩ :: Γ)
  | ty : Wf Γ → T.Wf Γ → x ∉ Γ.dom → Wf (⟨x, Binding.ty T⟩ :: Γ)

namespace Ty.Wf

open scoped Context
open List

variable {Γ Δ Θ : Env Var} {σ τ τ' γ δ : Ty Var}

omit [HasFresh Var] in
theorem perm_env (wf : σ.Wf Γ) (perm : Γ ~ Δ) (ok_Γ : Γ✓) (ok_Δ : Δ✓) : σ.Wf Δ := by
  induction wf generalizing Δ with
  | all _ _ _ _ ih => 
    apply all (free_union [Context.dom] Var) (by grind)
    intro X mem
    refine ih _ ?_ (Perm.cons _ perm) (nodupKeys_cons.mpr ?_) (nodupKeys_cons.mpr ?_)
    -- TODO: understand why we need simp here
    all_goals simp at mem; grind
  | _ => grind [perm_dlookup]

omit [HasFresh Var] in
theorem lc (wf : σ.Wf Γ) : σ.LC := by
  -- TODO: how to get grind to do this???
  induction wf with
  | all => apply LC.all (free_union Var) <;> grind
  | _   => grind

omit [HasFresh Var] in
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

omit [HasFresh Var] in
theorem weaken_head (wf : σ.Wf Γ) (ok : (Γ ++ Δ)✓) : σ.Wf (Γ ++ Δ) := by
  have : Γ ++ Δ = [] ++ Γ ++ Δ := by rfl
  grind [weaken]  

lemma narrow (wf : σ.Wf (Γ ++ [⟨X, Binding.sub τ⟩] ++ Δ))
  (ok : (Γ ++ [⟨X, Binding.sub τ'⟩] ++ Δ)✓) : 
    σ.Wf (Γ ++ [⟨X, Binding.sub τ'⟩] ++ Δ) := by
  generalize eq : (Γ ++ [⟨X, Binding.sub τ⟩] ++ Δ) = Θ at wf
  induction wf generalizing Γ with
  | var => sorry
  | all => sorry
  | _ => grind

lemma strengthen (wf : σ.Wf (Γ ++ [⟨x, Binding.ty U⟩] ++ Δ)) : σ.Wf (Γ ++ Δ) := by
  generalize eq : Γ ++ [⟨x, Binding.ty U⟩] ++ Δ = Θ at wf
  induction wf generalizing Γ with
  | var => sorry
  | all => sorry
  | _ => grind

lemma map_subst (wf_σ : σ.Wf (Γ ++ [⟨X, Binding.sub τ⟩] ++ Δ)) (wf_τ' : τ'.Wf Γ) : 
    (σ[X:=τ']).Wf <| (Γ ++ Δ).map_val (·[X:=τ']) := by
  generalize eq : Γ ++ [⟨X, Binding.sub τ⟩] ++ Δ = Θ at wf_σ
  induction wf_σ generalizing Γ τ' with
  | var => sorry
  | all => sorry
  | _ => grind

lemma open_lc (ok_Γ : Γ✓) (wf_all : (Ty.all σ τ).Wf Γ) (wf_δ : δ.Wf Γ) : (τ ^ᵞ δ).Wf Γ := by
  cases wf_all with | all L σ_wf cofin => sorry

omit [HasFresh Var] in
@[grind]
lemma to_ok (wf : Γ.Wf) : Γ✓ := by
  induction wf <;> constructor <;> first | assumption | grind

lemma from_bind_ty (wf : Γ.Wf) (bind : Binding.ty σ ∈ Γ.dlookup X) : σ.Wf Γ := 
  sorry
 
omit [HasFresh Var] in
lemma from_env_bind_ty (wf : Env.Wf ([⟨X, Binding.ty σ⟩] ++ Γ)) : σ.Wf Γ := by
  cases wf
  assumption

omit [HasFresh Var] in
lemma from_env_bind_sub (wf : Env.Wf ([⟨X, Binding.sub σ⟩] ++ Γ)) : σ.Wf Γ := by
  cases wf
  assumption

end Ty.Wf

namespace Env.Wf

variable {Γ Δ Θ : Env Var} {τ τ' : Ty Var}

lemma narrow (wf_env : Env.Wf (Γ ++ [⟨X, Binding.sub τ⟩] ++ Δ)) (wf_τ' : τ'.Wf Δ) : 
    Env.Wf (Γ ++ [⟨X, Binding.sub τ'⟩] ++ Δ) := by
  induction Γ generalizing τ τ' X
  · simp_all
    cases wf_env
    constructor <;> assumption
  · sorry
   
lemma strengthen (wf : Env.Wf <| Γ ++ [⟨X, Binding.ty τ⟩] ++ Δ) : Env.Wf <| Γ ++ Δ := by
  induction Γ generalizing Δ τ X
  case nil =>
    cases wf
    assumption
  case cons φ Φ ih =>
    sorry

lemma map_subst (wf_env : Env.Wf (Γ ++ [⟨X, Binding.sub τ⟩] ++ Δ)) (wf_τ' : τ'.Wf Δ) :
    Env.Wf <| (Γ ++ Δ).map_val (·[X:=τ']) := sorry

end Env.Wf

-- TODO : move these up???
open scoped Ty in
lemma Ty.nmem_fv_tm_open {σ : Ty Var} {X : Var} (nmem : X ∉ (σ ^ᵞ Y).fv) : X ∉ σ.fv := by
  induction σ generalizing X Y with
  | all => sorry
  | _ => simp [fv, open'] at * <;> grind

@[grind →]
lemma Ty.wf.nmem_fv {σ : Ty Var} (wf : σ.Wf Γ) (nmem : X ∉ Γ.dom) : X ∉ σ.fv := 
  sorry

open Context Ty Binding List in
lemma map_subst_nmem (Γ : Env Var) (X : Var) (σ : Ty Var) (wf : Γ.Wf) (nmem : X ∉ Γ.dom) :
    Γ = Γ.map_val (·[X:=σ]) := by
  induction wf <;> grind [keys_cons, toFinset_cons, Finset.mem_insert]

end LambdaCalculus.LocallyNameless.Fsub
