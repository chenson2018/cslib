/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.Basic
import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.Properties
import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.FullBeta
import Cslib.Data.Relation

/-! # β-confluence for the λ-calculus -/

universe u

variable {Var : Type u} 

namespace LambdaCalculus.LocallyNameless.Term

/-- A parallel β-reduction step. -/
@[aesop safe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet]) [constructors],
  reduction_sys paraRs "ₚ"]
inductive Parallel : Term Var → Term Var → Prop
/-- Free variables parallel step to themselves. -/
| fvar (x : Var) : Parallel (fvar x) (fvar x)
/-- A parallel left and right congruence rule for application. -/
| app : Parallel L L' → Parallel M M' → Parallel (app L M) (app L' M')
/-- Congruence rule for lambda terms. -/
| abs (xs : Finset Var) : 
    (∀ x ∉ xs, Parallel (m ^ fvar x) (m' ^ fvar x)) → Parallel (abs m) (abs m')
/-- A parallel β-reduction. -/
| beta (xs : Finset Var) : 
    (∀ x ∉ xs, Parallel (m ^ fvar x) (m' ^ fvar x) ) →
    Parallel n n' → 
    Parallel (app (abs m) n) (m' ^ n')

-- TODO: I think this could be generated along with `para_rs`
lemma para_rs_Red_eq {α} : (@paraRs α).Red = Parallel := by rfl

variable {M M' N N' : Term Var}

/-- The left side of a parallel reduction is locally closed. -/
@[aesop unsafe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma para_lc_l (step : M ⭢ₚ N) : LC M  := by
  induction step
  case abs _ _ xs _ ih => exact LC.abs xs _ ih
  case beta => refine LC.app (LC.abs ?_ _ ?_) ?_ <;> assumption
  all_goals constructor <;> assumption

/-- Parallel reduction is reflexive for locally closed terms. -/
@[aesop safe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma Parallel.lc_refl (M : Term Var) (lc : LC M) : M ⭢ₚ M := by
  induction lc
  all_goals constructor <;> assumption

-- TODO: better ways to handle this?
-- The problem is that sometimes when we apply a theorem we get out of our notation, so aesop can't
-- see they are the same, including constructors.
@[aesop safe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma Parallel.lc_refl' (M : Term Var) : LC M → Parallel M M := Parallel.lc_refl M

variable [HasFresh Var] [DecidableEq Var]

/-- The right side of a parallel reduction is locally closed. -/
@[aesop unsafe (rule_sets := [LambdaCalculus.LocallyNameless.ruleSet])]
lemma para_lc_r (step : M ⭢ₚ N) : LC N := by
  induction step
  case abs _ _ xs _ ih => exact LC.abs xs _ ih
  case beta => refine beta_lc (LC.abs ?_ _ ?_) ?_ <;> assumption
  all_goals constructor <;> assumption

omit [HasFresh Var] [DecidableEq Var] in
/-- A single β-reduction implies a single parallel reduction. -/
lemma step_to_para (step : M ⭢βᶠ N) : M ⭢ₚ N := by
  induction step <;> simp only [para_rs_Red_eq]
  case beta _ abs_lc _ => cases abs_lc with | abs xs _ => 
    apply Parallel.beta xs <;> intros <;> apply Parallel.lc_refl <;> aesop
  all_goals aesop (config := {enableSimp := false})

open FullBeta in
/-- A single parallel reduction implies a multiple β-reduction. -/
lemma para_to_redex (para : M ⭢ₚ N) : M ↠βᶠ N := by
  induction para
  case fvar => constructor
  case app _ _ _ _ l_para m_para redex_l redex_m =>
    trans
    · exact redex_app_l_cong redex_l (para_lc_l m_para)
    exact redex_app_r_cong redex_m (para_lc_r l_para)
  case abs t t' xs _ ih =>
    apply redex_abs_cong xs
    intros x mem
    exact ih x mem
  case beta m m' n n' xs para_ih para_n redex_ih redex_n =>
    have m'_abs_lc : LC m'.abs := by
      apply LC.abs xs
      intros _ mem
      exact para_lc_r (para_ih _ mem)
    calc
      m.abs.app n ↠βᶠ 
      m'.abs.app n := 
        redex_app_l_cong (redex_abs_cong xs (fun _ mem ↦ redex_ih _ mem)) (para_lc_l para_n)
      _           ↠βᶠ m'.abs.app n' := redex_app_r_cong redex_n m'_abs_lc
      _           ⭢βᶠ m' ^ n'       := beta m'_abs_lc (para_lc_r para_n)

/-- Multiple parallel reduction is equivalent to multiple β-reduction. -/
theorem parachain_iff_redex : M ↠ₚ N ↔ M ↠βᶠ N := by
  refine Iff.intro ?chain_redex ?redex_chain <;> intros h <;> induction' h <;> try rfl
  case redex_chain.tail redex chain => exact Relation.ReflTransGen.tail chain (step_to_para redex)
  case chain_redex.tail para  redex => exact Relation.ReflTransGen.trans redex (para_to_redex para)

/-- Parallel reduction respects substitution. -/
lemma para_subst (x : Var) (pm : M ⭢ₚ M') (pn : N ⭢ₚ N') : M[x := N] ⭢ₚ M'[x := N'] := by
  induction pm
  case fvar => aesop
  case beta _ _ _ _ xs _ _ ih _ => 
    simp only [open']
    rw [subst_open _ _ _ _ _ (para_lc_r pn)]
    refine Parallel.beta (xs ∪ {x}) ?_ (by assumption)
    · intros y ymem
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at ymem
      push_neg at ymem
      rw [
        subst_def, 
        subst_open_var _ _ _ _ _ (para_lc_r pn), 
        subst_open_var _ _ _ _ _ (para_lc_l pn)
      ] <;> aesop
  case app => constructor <;> assumption
  case abs u u' xs mem ih => 
    apply Parallel.abs (xs ∪ {x})
    intros y ymem
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at ymem
    repeat rw [subst_def]
    push_neg at ymem
    rw [
      subst_open_var _ _ _ _ ?_ (para_lc_l pn), 
      subst_open_var _ _ _ _ ?_ (para_lc_r pn)
    ] <;> aesop

/-- Parallel substitution respects closing and opening. -/
lemma para_open_close (x y z) (para : M ⭢ₚ M') (_ : y ∉ M.fv ∪ M'.fv ∪ {x}) :
    M⟦z ↜ x⟧⟦z ↝ fvar y⟧ ⭢ₚ M'⟦z ↜ x⟧⟦z ↝ fvar y⟧ := by
  simp only [Finset.union_assoc, Finset.mem_union, Finset.mem_singleton, not_or] at *
  rw [open_close_to_subst _ _ _ _ (para_lc_l para), open_close_to_subst _ _ _ _ (para_lc_r para)]
  apply para_subst _ para
  constructor

/-- Parallel substitution respects fresh opening. -/
lemma para_open_out (L : Finset Var) (mem : ∀ x, x ∉ L → (M ^ fvar x) ⭢ₚ N ^ fvar x)
    (para : M' ⭢ₚ N') : (M ^ M') ⭢ₚ (N ^ N') := by
  let ⟨x, qx⟩ := fresh_exists (L ∪ N.fv ∪ M.fv)
  simp only [Finset.union_assoc, Finset.mem_union, not_or] at qx
  obtain ⟨q1, q2, q3⟩ := qx
  rw [subst_intro x M' _ q3 (para_lc_l para), subst_intro x N' _ q2 (para_lc_r para)]
  exact para_subst x (mem x q1) para

@[simp]
def takahashi : Term Var → Term Var
| bvar x => bvar x
| fvar i => fvar i
| abs M => abs M.takahashi
| app (abs N) M => N.takahashi ^ M.takahashi
| app L R => app L.takahashi R.takahashi

-- TODO: not sure this is true...
theorem takahashi_openRec {M : Term Var} : M⟦k ↝ fvar x⟧.takahashi = M.takahashi⟦k ↝ fvar x⟧ := by
  revert k x
  induction M using takahashi.induct
  case case4 l r ih_l ih_r => 
    intros k x
    sorry
  case case5 l _ _ _ _ => induction l <;> aesop
  all_goals aesop

--@[simp]
--theorem takahashi_open {M : Term Var} : (M ^ fvar x).takahashi = M.takahashi ^ fvar x := by
--  exact takahashi_openRec

theorem takahashi_triangle (M N : Term Var) (para : M ⭢ₚ N) : N ⭢ₚ M.takahashi := by
  induction para
  case fvar => aesop
  case abs L q w => 
    refine Parallel.abs L ?_
    sorry
  case beta L _ _ _ np => 
    refine para_open_out L ?_ np
    sorry
  case app L' _ _ _ L_L' _ Lt Rt =>
    induction L'
    case abs =>
      cases L_L'
      cases Lt
      next xs _ => exact Parallel.beta xs (by aesop) Rt
    all_goals constructor <;> aesop

theorem para_diamond : Diamond (@Parallel Var) := triangle_diamond takahashi_triangle

/-- Parallel reduction is confluent. -/
theorem para_confluence : Confluence (@Parallel Var) := 
  Relation.ReflTransGen.diamond_confluence para_diamond

/-- β-reduction is confluent. -/
theorem confluence_beta : Confluence (@FullBeta Var) := by
  simp only [Confluence]
  have eq : Relation.ReflTransGen (@Parallel Var) = Relation.ReflTransGen (@FullBeta Var) := by
    ext
    exact parachain_iff_redex
  rw [←eq]
  exact @para_confluence Var _ _

end LambdaCalculus.LocallyNameless.Term
