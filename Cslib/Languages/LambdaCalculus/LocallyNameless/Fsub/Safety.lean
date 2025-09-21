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

-- TODO: wrong namespace!
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
lemma TransOn_all (δ : Ty Var) : TransOn δ := by
  intro Γ σ τ sub₁ sub₂ 
  have δ_lc : δ.LC := by grind
  --let δ' := δ 
  induction δ_lc generalizing Γ σ τ
  case top => cases sub₁ <;> cases sub₂ <;> grind
  case var =>
    -- TODO: not sure about this case...
    cases sub₁ <;> cases sub₂
    case trans_tvar.trans_tvar X' σ' X mem sub σ mem' sub' => 
      by_cases eq : X = X'
      · have eq : σ = σ' := by grind
        grind
      · sorry
    all_goals grind
  case arrow σ' τ' _ _ _ _ => 
    generalize eq : σ'.arrow τ' = γ at sub₁
    induction sub₁ <;> grind [cases Sub]
  case sum σ' τ' _ _ _ _ => 
    generalize eq : σ'.sum τ' = γ at sub₁
    induction sub₁ <;> grind [cases Sub]
  case all σ' τ' _ _ _ _ _ => 
    generalize eq : σ'.all τ' = γ at sub₁
    induction sub₁
    case all =>
      cases eq
      cases sub₂
      case refl.top Γ σ'' τ'' _ _ _ _ _ _ _ => 
        have : Sub Γ (σ''.all τ'') (σ'.all τ') := by apply all (free_union Var) <;> grind
        grind
      case refl.all Γ _ τ'' _ _ s1 σ τ _ _ s2 _ _ => 
        apply all (free_union Var)
        grind
        intro X nmem
        specialize s1 X (by grind)
        specialize s2 X (by grind)
        have s1' : Sub (⟨X, Binding.sub σ⟩ :: Γ) (τ'' ^ᵞ fvar X) (τ' ^ᵞ fvar X) := by
          have eq : ∀ σ, ⟨X, Binding.sub σ⟩ :: Γ = [] ++ [⟨X, Binding.sub σ⟩] ++ Γ := by grind
          rw [eq]
          apply Sub.narrow_aux (δ := σ') <;> grind
        grind
    all_goals grind

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

lemma Typing.weaken (der : Typing (Γ ++ Δ) t τ) (wf : (Γ ++ Θ ++ Δ).Wf) : 
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

omit [HasFresh Var] in
lemma Sub.strengthen (sub : Sub (Γ ++ [⟨X, Binding.ty δ⟩] ++ Δ) σ τ) :  Sub (Γ ++ Δ) σ τ := by
  generalize eq : Γ ++ [⟨X, Binding.ty δ⟩] ++ Δ = Θ at sub
  induction sub generalizing Γ 
  case all => apply Sub.all (free_union Var) <;> grind
  all_goals grind [Ty.Wf.strengthen, Env.Wf.strengthen]

lemma Typing.narrow (sub : Sub Δ δ δ') (der : Typing (Γ ++ [⟨X, Binding.sub δ'⟩] ++ Δ) t τ) :
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
  case abs τ L _ _ => 
    cases eq
    cases sub
    split_ands
    · assumption
    · exists τ, L
      grind
  case sub Γ _ τ τ' _ _ ih => 
    subst eq
    have sub' : Sub Γ τ (γ.arrow δ) := by trans τ' <;> grind
    obtain ⟨_, δ', L, _⟩ := ih sub' (by rfl)
    split_ands
    · assumption
    · exists δ', L
  all_goals grind

lemma Typing.tabs_inv (der : Typing Γ (tabs γ' t) τ) (sub : Sub Γ τ (all γ δ)) :
     Sub Γ γ γ'
  ∧ ∃ δ' L, ∀ X ∉ (L : Finset Var),
     Typing ([⟨X, Binding.sub γ⟩] ++ Γ) (t ^ᵗᵞ fvar X) (δ' ^ᵞ fvar X)
     ∧ Sub ([⟨X, Binding.sub γ⟩] ++ Γ) (δ' ^ᵞ fvar X) (δ ^ᵞ fvar X) := by
  generalize eq : tabs γ' t = e at der
  induction der generalizing γ δ t γ'
  case tabs σ Γ _ τ L der _ =>
    cases sub with | all L' sub => 
    split_ands
    · grind
    · exists τ, L ∪ L'
      intro X _
      have eq : [⟨X, Binding.sub γ⟩] ++ Γ = [] ++ [⟨X, Binding.sub γ⟩] ++ Γ :=by rfl
      grind [Typing.narrow]
  case sub Γ _ τ τ' _ _ ih => 
    subst eq
    have sub' : Sub Γ τ (γ.all δ) := by trans τ' <;> grind
    obtain ⟨_, δ', L, _⟩ := ih sub' (by rfl)
    split_ands
    · assumption
    · exists δ', L
  all_goals grind

lemma Typing.inl_inv (der : Typing Γ (inl t) τ) (sub : Sub Γ τ (sum γ δ)) :
    ∃ γ', Typing Γ t γ' ∧ Sub Γ γ' γ := by
  generalize eq : t.inl =t at der
  induction der generalizing γ δ
  case sub Γ _ τ τ' _ _ ih => 
    -- TODO: tell grind to use trans??
    have sub' : Sub Γ τ (γ.sum δ) := by trans τ' <;> grind
    grind  
  all_goals grind [cases Sub]

lemma Typing.inr_inv (der : Typing Γ (inr t) T) (sub : Sub Γ T (sum γ δ)) :
    ∃ δ', Typing Γ t δ' ∧ Sub Γ δ' δ := by
  generalize eq : t.inr =t at der
  induction der generalizing γ δ
  case sub Γ _ τ τ' _ _ ih => 
    -- TODO: tell grind to use trans??
    have sub' : Sub Γ τ (γ.sum δ) := by trans τ' <;> grind
    grind  
  all_goals grind [cases Sub]

lemma Typing.preservation (der : Typing Γ t τ) (step : Red t t') : Typing Γ t' τ := by
  induction der generalizing t'
  case app der₁ _ _ _ => 
    cases step with
    | abs => sorry
    | _ => grind
  case tapp => 
    cases step
    · grind
    · sorry
  case let' => 
    cases step
    · sorry
    · sorry
  case case => 
    cases step
    · sorry
    · sorry
    · sorry
  all_goals grind [cases Red]

omit [HasFresh Var] in
lemma Typing.canonical_form_abs (val : Value t) (der : Typing [] t (arrow σ τ)) :
    ∃ δ t', t = abs δ t' := by
  generalize eq  : σ.arrow τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Value, cases Sub]

omit [HasFresh Var] in
lemma Typing.canonical_form_tabs (val : Value t) (der : Typing [] t (all σ τ)) :
    ∃ δ t', t = tabs δ t' := by
  generalize eq  : σ.all τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Value, cases Sub]

omit [HasFresh Var] in
lemma Typing.canonical_form_sum (val : Value t) (der : Typing [] t (sum σ τ)) :
    ∃ t', t = inl t' ∨ t = inr t' := by
  generalize eq  : σ.sum τ = γ at der
  generalize eq' : [] = Γ at der
  induction der generalizing σ τ <;> grind [cases Value, cases Sub]

lemma Typing.progress (der : Typing [] t τ) : Value t ∨ ∃ t', Red t t' := by
  generalize eq : [] = Γ at der
  have der' : Typing Γ t τ := by assumption
  induction der <;> subst eq <;> simp only [forall_const] at *
  case var mem => grind
  case app t₁ _ _ t₂ l r ih_l ih_r => 
    right
    cases ih_l l with
    | inl val_l => 
        cases ih_r r with
        | inl val_r => 
            have ⟨σ, t₁, eq⟩ := Typing.canonical_form_abs val_l l
            exists t₁ ^ᵗᵗ t₂
            grind
        | inr red_r => 
            obtain ⟨t₂', _⟩ := red_r
            exists t₁.app t₂'
            grind
    | inr red_l => 
        obtain ⟨t₁', _⟩ := red_l
        exists t₁'.app t₂
        grind
  case tapp σ' der _ ih => 
    right
    specialize ih der
    cases ih with
    | inl val => 
        obtain ⟨_, t, _⟩ := Typing.canonical_form_tabs val der
        exists t ^ᵗᵞ σ'
        grind
    | inr red => 
        obtain ⟨t', _⟩ := red
        exists tapp t' σ'
        grind
  case let' t₁ σ t₂ τ L der _ _ ih => 
    right
    cases ih der with
    | inl _ => 
        exists t₂ ^ᵗᵗ t₁
        grind
    | inr red => 
        obtain ⟨t₁', _⟩ := red
        exists t₁'.let' t₂
        grind
  -- TODO: inverse not used here???
  case inl der _ ih =>
    cases (ih der) with
    | inl val => grind
    | inr red => 
        right
        obtain ⟨t', _⟩ := red
        exists inl t'
        grind
  case inr der _ ih =>
    cases (ih der) with
    | inl val => grind
    | inr red => 
        right
        obtain ⟨t', _⟩ := red
        exists inr t'
        grind
  case case t₁ _ _ t₂ _ t₃ _ der _ _ _ _ ih => 
    right
    cases ih der with
    | inl val => 
        have ⟨t₁, lr⟩ := Typing.canonical_form_sum val der
        cases lr <;> [exists t₂ ^ᵗᵗ t₁; exists t₃ ^ᵗᵗ t₁] <;> grind
    | inr red => 
        obtain ⟨t₁', _⟩ := red
        exists t₁'.case t₂ t₃
        grind
  case sub => grind
  case abs σ _ τ L _ _=> 
    left
    constructor
    apply LC.abs L <;> grind
  case tabs L _ _=>
    left
    constructor
    apply LC.tabs L <;> grind

end Ty

end LambdaCalculus.LocallyNameless.Fsub
