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

namespace Ty

open Ty.Wf Env.Wf Context List

namespace Sub

omit [HasFresh Var] in
@[grind <=]
lemma refl (wf_Γ : Γ.Wf) (wf_σ : σ.Wf Γ) : Sub Γ σ σ := by
  induction wf_σ with
  | all => apply all (free_union [Context.dom] Var) <;> grind
  | _ => grind

omit [HasFresh Var] in
lemma weaken (sub : Sub (Γ ++ Θ) σ σ') (wf : (Γ ++ Δ ++ Θ).Wf) : Sub (Γ ++ Δ ++ Θ) σ σ' := by
  generalize eq : Γ ++ Θ = ΓΘ at sub
  induction sub generalizing Γ 
  case trans_tvar σ _ _ X mem _ _=> 
    have : (Γ ++ Δ ++ Θ).Perm (Δ ++ Γ ++ Θ) := by grind [perm_append_comm_assoc]
    grind [dlookup_append, dlookup_eq_none, keys_append]
  case all σ _ _ _ _ _ _ _ ih => 
    subst eq
    apply all (free_union [Context.dom] Var)
    · grind
    · intro X mem
      have wf : Env.Wf ((⟨X, Binding.sub σ⟩ :: Γ) ++ Δ ++ Θ) := by
        constructor
        grind
        grind
        -- TODO: still problems with grind here...
        simp_all [keys_append, dom]
      grind
  all_goals grind  

@[simp, grind =]
def TransOn (δ : Ty Var) := ∀ Γ σ τ, Sub Γ σ δ → Sub Γ δ τ → Sub Γ σ τ 

-- TODO: make the params of this match up with `narrow`, or maybe even inline it?
-- TODO: more grind work here
omit [HasFresh Var] in
lemma narrow_aux (trans : TransOn δ) (sub₁ : Sub (Γ ++ [⟨X, Binding.sub δ⟩] ++ Δ) σ τ)
    (sub₂ : Sub Δ δ' δ) : Sub (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) σ τ := by
  generalize eq : Γ ++ [⟨X, Binding.sub δ⟩] ++ Δ = Θ at sub₁ 
  induction sub₁ generalizing Γ δ
  case trans_tvar σ _ σ' X' mem sub ih => 
    subst eq
    by_cases eq : X = X'
    · subst eq
      -- TODO: this pattern appears often
      have p : ∀ δ, Γ ++ [⟨X, Binding.sub δ⟩] ++ Δ ~ ⟨X, Binding.sub δ⟩ :: (Γ ++ Δ) := by simp
      apply Sub.trans_tvar (σ := δ')
      · rw [List.perm_dlookup (p := p δ')] <;> grind
      · apply trans
        · have : Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ = [] ++ (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) := by rfl
          grind [Sub.weaken]
        · rw [perm_dlookup (p := p δ), dlookup_cons_eq] at mem <;> grind
    · grind
  case all => apply Sub.all (free_union Var) <;> grind
  all_goals grind [Ty.Wf.narrow, Env.Wf.narrow]

@[grind]
lemma TransOn_all (δ : Ty Var) : TransOn δ := sorry

instance (Γ : Env Var) : Trans (Sub Γ) (Sub Γ) (Sub Γ) where
  trans s1 s2 := TransOn_all _ _ _ _ s1 s2

lemma narrow (sub_δ : Sub Δ δ δ') (sub_narrow : Sub (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) σ τ) :
    Sub (Γ ++ [⟨X, Binding.sub δ⟩] ++ Δ) σ τ := by
  apply narrow_aux (δ := δ') <;> grind

lemma map_subst (sub₁ : Sub (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) σ τ) (sub₂ : Sub Δ δ δ') :
    Sub (Γ.map_val (·[X:=δ]) ++ Δ) (σ[X:=δ]) (τ[X:=δ]) := by
  generalize eq : Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ = Θ at sub₁ 
  induction sub₁ generalizing Γ
  case trans_tvar σ Γ σ' X' mem sub ih =>
    subst eq
    by_cases eq : X' = X <;> simp only [←Ty.subst_def, Ty.subst, eq, reduceIte] <;> simp only [Ty.subst_def]
    · trans
      · rw [←List.nil_append (map_val _ _ ++ _), ←List.append_assoc]
        apply Sub.weaken
        exact sub₂
        grind
      · sorry          
    · have : (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ)✓ := by grind
      have : X ∉ dom Γ := sorry
      have mem' : Binding.sub σ ∈ dlookup X' (Γ ++ Δ) := by grind
      have mem'' : Binding.sub σ ∈ dlookup X' (Γ.map_val (·[X:=δ]) ++ Δ) := sorry
      apply Sub.trans_tvar mem''
      sorry
  case all σ _ τ' τ _ _ _ _ ih =>
    apply Sub.all (free_union Var)
    · grind
    · subst eq
      simp only [Ty.subst_def]
      intro X' nmem
      rw [←Ty.open_subst_var, ←Ty.open_subst_var]
      have := @ih X' (by grind) (⟨X', Binding.sub σ⟩ :: Γ)
      all_goals grind [Binding.subst_sub]
  all_goals grind [Ty.Wf.map_subst, Env.Wf.map_subst]

end Sub

lemma Typing.wekaen (der : Typing (Γ ++ Δ) t τ) (wf : (Γ ++ Θ ++ Δ).Wf) : 
    Typing (Γ ++ Θ ++ Δ) t τ := by
  generalize eq : Γ ++ Δ = ΓΔ at der
  induction der generalizing Γ wf
  case var mem => 
    subst eq
    have s : Γ ++ Δ <+ (Γ ++ Θ ++ Δ) := by grind
    -- TODO: grind here???
    apply Typing.var wf
    apply sublist_dlookup (s := s) <;> grind
  case abs σ _ _ _ _ h h' => 
    subst eq
    apply Typing.abs (free_union Var)
    intro X nmem
    sorry
  case tabs => sorry
  case let' => sorry
  case case => sorry
  all_goals grind [Sub.weaken, Ty.Wf.from_env_bind_ty, Ty.Wf.from_env_bind_sub, Ty.Wf.weaken]

lemma Sub.strengthen (sub : Sub (Γ ++ [⟨X, Binding.ty δ⟩] ++ Δ) σ τ) :  Sub (Γ ++ Δ) σ τ := 
  sorry

lemma Typing.narrow (sub : Sub Γ δ δ') (der : Typing (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) t τ) :
    Typing (Γ ++ [⟨X, Binding.sub δ⟩] ++ Δ) t τ := sorry

lemma Typing.subst_tm (der : Typing (Γ ++ [⟨X, Binding.ty σ⟩] ++ Δ) t τ) (der_sub : Typing Δ s σ) :
    Typing (Γ ++ Δ) (t[X := s]) τ := sorry

lemma Typing.subst_ty (der : Typing (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) t τ) (sub : Sub Γ δ δ') : 
    Typing (Γ.map_val (·[X := δ]) ++ Δ) (t[X := δ]) (τ[X := δ]) := sorry

open Term Ty

lemma Typing.abs_inv (der : Typing Γ (abs γ' t) τ) (sub : Sub Γ τ (arrow γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ x ∉ (L : Finset Var), 
    Typing ([⟨x, Binding.ty γ'⟩] ++ Γ) (t ^ᵗᵗ .fvar x) δ' ∧ Sub Γ δ' δ := by
  generalize eq : Term.abs γ' t = e at der
  induction der generalizing t γ' γ δ
  case abs => sorry
  case sub => sorry
  all_goals grind

lemma Typing.tabs_inv (der : Typing Γ (tabs γ' t) τ) (sub : Sub Γ τ (all γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ X ∉ (L : Finset Var),
     Typing ([⟨X, Binding.sub γ⟩] ++ Γ) (t ^ᵗᵞ fvar X) (δ' ^ᵞ fvar X)
     ∧ Sub ([⟨X, Binding.sub γ⟩] ++ Γ) (δ' ^ᵞ fvar X) (δ ^ᵞ fvar X) := sorry

lemma Typing.inl_inv (der : Typing Γ (inl t) τ) (sub : Sub Γ τ (sum γ δ)) :
  ∃ γ', Typing Γ t γ' ∧ Sub Γ γ' γ := sorry    

lemma Typing.inr_inv (der : Typing Γ (inr t) T) (sub : Sub Γ T (sum γ δ)) :
  ∃ δ', Typing Γ t δ' ∧ Sub Γ δ' δ := sorry

lemma Typing.preservation (der : Typing Γ t τ) (step : Red t t') : Typing Γ t' τ := 
  sorry

lemma Typing.canonical_form_abs (val : Value t) (der : Typing [] t (arrow σ τ)) :
  ∃ δ t', t = abs δ t' := sorry

lemma Typing.canonical_form_tabs (val : Value t) (der : Typing [] t (all σ τ)) :
  ∃ δ t', t = tabs δ t' := sorry

lemma Typing.canonical_form_sum (val : Value t) (der : Typing [] t (sum σ τ)) :
  ∃ t', t = inl t' ∨ t = inr t' := sorry

lemma Typing.progress (der : Typing [] t τ) : Value t ∨ ∃ t', Red t t' := sorry

end Ty

end LambdaCalculus.LocallyNameless.Fsub
