/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Computability.LambdaCalculus.LocallyNameless.Fsub.Basic

/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u} [HasFresh Var] [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

open Ty Term

omit [HasFresh Var] [DecidableEq Var] in
/-- An opening appearing in both sides of an equality of types can be removed. -/
@[scoped grind]
lemma Ty.openRec_lc_aux (T : Ty Var) j V i U (neq : i ≠ j) (h : T⟦j ↝ V⟧ᵞ = T⟦j ↝ V⟧ᵞ⟦i ↝ U⟧ᵞ) : 
    T = T⟦i ↝ U⟧ᵞ := by induction T generalizing j i <;> grind

/-- A locally closed type is unchanged by opening. -/
@[scoped grind =_]
lemma Ty.openRec_lc (T : Ty Var) U k (lc : T.LC) : T = T⟦k ↝ U⟧ᵞ := by
  induction lc generalizing k
  case all => 
    -- TODO: how to tell grind to try `free_union`?
    let ⟨x, _⟩ := fresh_exists <| free_union Var
    grind
  all_goals grind

omit [HasFresh Var] in
/-- Substitution of a free variable not present in a type leaves it unchanged. -/
@[scoped grind]
lemma Ty.subst_fresh (Z : Var) (U T : Ty Var) (nmem : Z ∉ T.fv) : T = T[Z := U] := by
  induction T <;> grind

/-- Substitution of a locally closed type distributes with opening. -/
@[scoped grind]
lemma Ty.subst_openRec (T1 T2 : Ty Var) (X : Var) (P : Ty Var) k (lc : P.LC) : 
    (T1⟦k ↝ T2⟧ᵞ)[X := P] = T1[X := P]⟦k ↝ T2[X := P]⟧ᵞ := by
  induction T1 generalizing k <;> grind

/-- Specialize `Ty.subst_openRec` to the first opening. -/
lemma Ty.subst_open (T1 T2 : Ty Var) (X : Var) (P : Ty Var) (lc : P.LC) :
    (T1 ^ᵞ T2)[X := P] = T1[X := P] ^ᵞ T2[X := P] := subst_openRec _ _ _ _ _ lc

/-- Specialize `Ty.subst_open` to free variables. -/
lemma Ty.subst_open_var (X Y : Var) (P T : Ty Var) (neq : Y ≠ X) (lc : P.LC) :
    (T ^ᵞ fvar Y)[X := P] = (T[X := P]) ^ᵞ fvar Y := by grind

omit [HasFresh Var] in
/-- Opening to a type is equivalent to opening to a free variable and substituting. -/
@[scoped grind]
lemma Ty.openRec_subst_intro (X : Var) (T2 U : Ty Var) (k : ℕ) (nmem : X ∉ T2.fv) :
    T2⟦k ↝ U⟧ᵞ = (T2⟦k ↝ fvar X⟧ᵞ)[X := U] := by
  induction T2 generalizing U k <;> grind

omit [HasFresh Var] in
/-- Specialize `Ty.openRec_subst_intro` to the first opening. -/
lemma Ty.open_subst_intro (X : Var) (T2 U : Ty Var) (nmem : X ∉ T2.fv) :
    T2 ^ᵞ U = (T2 ^ᵞ fvar X)[X := U] := openRec_subst_intro _ _ _ _ nmem

namespace Term

omit [HasFresh Var] [DecidableEq Var] in
@[scoped grind]
lemma openRec_ty_lc_aux₁ (e : Term Var) j (u : Term Var) i (P : Ty Var) 
    (eq : e⟦j ↝ u⟧ᵗᵗ = e⟦j ↝ u⟧ᵗᵗ⟦i ↝ P⟧ᵗᵞ) : e = e⟦i ↝ P⟧ᵗᵞ
  := by induction e generalizing j i <;> grind

omit [HasFresh Var] [DecidableEq Var] in
@[scoped grind]
lemma openRec_ty_lc_aux₂ (e : Term Var) j (Q : Ty Var) i (P : Ty Var) : 
    i ≠ j → e⟦j ↝ Q⟧ᵗᵞ = e⟦j ↝ Q⟧ᵗᵞ⟦i ↝ P⟧ᵗᵞ → e = e⟦i ↝ P⟧ᵗᵞ := by
  induction e generalizing j i <;> grind

/-- An opening (term to type) appearing in both sides of an equality of terms can be removed. -/
@[scoped grind]
lemma openRec_ty_lc (e : Term Var) (U : Ty Var) k (e_lc : e.LC) : e = e⟦k ↝ U⟧ᵗᵞ := by
  induction e generalizing k
  case abs T t ih =>
    simp [openRec_ty]
    refine ⟨by grind, ?_⟩
    cases e_lc with | abs L T_lc cofin =>
    have ⟨x, free⟩ := fresh_exists L
    ----rw [←openRec_ty_lc_aux₁ (j := 0) (u := fvar x)]
    ----rw [←openRec_ty_lc_aux₂ (j := 0) (Q := fvar x)]
    sorry    
  case tabs => sorry
  case let' => sorry
  case case => sorry
  all_goals grind

omit [HasFresh Var] in
/-- Substitution of a free type variable not present in a term leaves it unchanged. -/
lemma subst_ty_fresh (X : Var) (U : Ty Var) (e : Term Var) (nmem : X ∉ e.fv_ty) : 
    e = e [X := U] := by induction e <;> grind

/-- Substitution of a locally closed type distributes with term opening to a type . -/
@[scoped grind]
lemma subst_openRec_ty (e : Term Var) T (X : Var) (U : Ty Var) k (U_lc : U.LC) : 
    (e⟦k ↝ T⟧ᵗᵞ)[X := U] = (e[X := U])⟦k ↝  T[X := U]⟧ᵗᵞ := by
  induction e generalizing k <;> grind

/-- Specialize `subst_openRec_ty` to the first opening. -/
lemma subst_open_ty (e : Term Var) T (X : Var) (U : Ty Var) (U_lc : U.LC) : 
    (e ^ᵗᵞ T)[X := U] = e[X := U] ^ᵗᵞ T[X := U] := subst_openRec_ty e T X U 0 U_lc

/-- Specialize `subst_open_ty` to free variables. -/
lemma subst_open_var_ty (X Y : Var) (U : Ty Var) (e : Term Var) (neq : X ≠ Y) (U_lc : U.LC) :
    (e ^ᵗᵞ Ty.fvar Y)[X := U] = e[X := U] ^ᵗᵞ Ty.fvar Y := by grind

omit [HasFresh Var]
/-- Opening to a term to a type is equivalent to opening to a free variable and substituting. -/
lemma openRec_subst_intro_ty (X : Var) (e : Term Var) (U : Ty Var) k (nmem : X ∉ e.fv_ty) : 
    e⟦k ↝ U⟧ᵗᵞ = (e⟦k ↝ Ty.fvar X⟧ᵗᵞ)[X := U] := by
  induction e generalizing X U k <;> grind

/-- Specialize `openRec_subst_intro_ty` to the first opening. -/
lemma open_subst_intro_ty (X : Var) (e : Term Var) (U : Ty Var) (nmem : X ∉ e.fv_ty) : 
    e ^ᵗᵞ U = (e ^ᵗᵞ Ty.fvar X)[X := U] := openRec_subst_intro_ty X e U 0 nmem

omit [DecidableEq Var] in
@[scoped grind]
lemma openRec_tm_lc_aux₁ (e : Term Var) j v u i (neq : i ≠ j)
    (eq : e⟦j ↝ v⟧ᵗᵗ = e⟦j ↝ v⟧ᵗᵗ⟦i ↝ u⟧ᵗᵗ) : e = e⟦i ↝ u⟧ᵗᵗ := by
  induction e generalizing i j <;> grind

omit [DecidableEq Var] in
@[scoped grind]
lemma openRec_tm_lc_aux₂ (e : Term Var) j V u i (eq : e⟦j ↝ V⟧ᵗᵞ = e⟦j ↝ V⟧ᵗᵞ⟦i ↝ u⟧ᵗᵗ) :
    e = e⟦i ↝ u⟧ᵗᵗ := by
  induction e generalizing i j <;> grind

/-- An opening (term to term) appearing in both sides of an equality of terms can be removed. -/
@[scoped grind]
lemma openRec_tm_lc (u e : Term Var) k (e_lc : e.LC) : e = e⟦k ↝ u⟧ᵗᵗ := by
  induction e_lc generalizing k
  case abs => sorry
  case tabs => sorry
  case let' => sorry
  case case => sorry
  all_goals grind

/-- Substitution of a term variable not present in a term leaves it unchanged. -/
lemma subst_tm_fresh x (u e : Term Var) (nmem : x ∉ e.fv_tm) : e = e[x := u] := by
  induction e <;> grind

/-- Term substitution distributes with term opening . -/
lemma subst_tm_openRec_tm (e1 e2 : Term Var) (x : Var) (u : Term Var) k (u_lc : u.LC) :
    (e1⟦k ↝ e2⟧ᵗᵗ)[x := u] = (e1[x := u])⟦k ↝  e2[x := u]⟧ᵗᵗ := by
  induction e1 generalizing k <;> grind

/-- Specialize `subst_openRec_tm` to the first opening. -/
lemma subst_tm_open_tm (e1 e2 : Term Var) (x : Var) (u : Term Var) (u_lc : u.LC) :
    (e1 ^ᵗᵗ e2)[x := u] = (e1[x := u]) ^ᵗᵗ e2[x := u] := subst_tm_openRec_tm e1 e2 x u 0 u_lc

/-- Specialize `subst_open_tm` to free variables. -/
lemma subst_tm_open_var_tm (e : Term Var) (x y : Var) (u : Term Var) (neq : y ≠ x) (u_lc : u.LC) :
    (e ^ᵗᵗ fvar y)[x := u] = (e[x := u]) ^ᵗᵗ fvar y := by grind [subst_tm_open_tm]

/-- Type substitution distributes with term opening . -/
lemma subst_ty_openRec_tm (e1 e2 : Term Var) (Z : Var) (P : Ty Var) k : 
    (e1⟦k ↝ e2⟧ᵗᵗ)[Z := P] = (e1[Z := P])⟦k ↝ e2[Z := P]⟧ᵗᵗ := sorry

/-- Specialize `subst_ty_openRec_tm` to the first opening. -/
lemma subst_ty_open_tm (e1 e2 : Term Var) (Z : Var) (P : Ty Var) : 
    (e1 ^ᵗᵗ e2)[Z := P] = (e1[Z := P]) ^ᵗᵗ e2[Z := P] := subst_ty_openRec_tm e1 e2 Z P 0

/-- Specialize `subst_ty_openRec_tm` to the first opening. -/
lemma subst_ty_open_var_tm (e : Term Var) (Z x : Var) (P : Ty Var) : 
    (e ^ᵗᵗ fvar x)[Z := P] = (e[Z := P]) ^ᵗᵗ fvar x := by grind [subst_ty_open_tm]

lemma subst_tm_openRec_ty (e : Term Var) (P : Ty Var) (z : Var) (u : Term Var) k (u_lc : u.LC) :
    (e⟦k ↝ P⟧ᵗᵞ)[z := u] = e[z := u]⟦k ↝ P⟧ᵗᵞ := sorry

lemma subst_tm_open_ty (e : Term Var) (P : Ty Var) (z : Var) (u : Term Var) (u_lc : u.LC) :
    (e ^ᵗᵞ P)[z := u] = e[z := u] ^ᵗᵞ P := by apply subst_tm_openRec_ty (k := 0) (u_lc := u_lc)

lemma subst_tm_open_var_ty (e : Term Var) (z X : Var) (u : Term Var) (u_lc : u.LC) :
    (e ^ᵗᵞ Ty.fvar X)[z := u] = e[z := u] ^ᵗᵞ Ty.fvar X := subst_tm_open_ty _ _ _ _ u_lc

lemma openRec_subst_intro_tm (x : Var) (e u : Term Var) k (nmem : x ∉ e.fv_tm) :
    e⟦k ↝ u⟧ᵗᵗ = (e⟦k ↝ fvar x⟧ᵗᵗ)[x := u] := by
  induction e generalizing k <;> grind

lemma open_subst_intro_tm (x : Var) (e u : Term Var) (nmem : x ∉ e.fv_tm) :
    e ^ᵗᵗ u = (e ^ᵗᵗ fvar x)[x := u] := openRec_subst_intro_tm x e u 0 nmem

end Term

@[scoped grind =>]
lemma Ty.subst_lc (Z : Var) (P T : Ty Var) (T_lc : T.LC) (P_lc : P.LC) : T[Z := P].LC := by
  induction T_lc
  case all => apply LC.all (free_union Var) <;> grind
  -- TODO : make these forward rules?
  all_goals grind [LC.top, LC.var, LC.arrow, LC.sum]
    
lemma Term.subst_ty_lc (Z : Var) (P : Ty Var) (e : Term Var) (e_lc : e.LC) (P_lc : P.LC) :
    e[Z := P].LC := by
  induction e_lc
  case abs => sorry
  case tabs => sorry
  case let' => sorry
  case case => sorry
  -- TODO : make these forward rules?
  all_goals grind [LC.var, LC.app, LC.inl, LC.inr, LC.tapp]

lemma Term.subst_tm_lc (z : Var) (e1 e2 : Term Var) (e1_lc : e1.LC) (e2_lc : e2.LC) :
    e1[z := e2].LC := sorry

omit [HasFresh Var] [DecidableEq Var] in
lemma Term.lc_let_from_body (e1 e2 : Term Var) (e1_lc : e1.LC) (h : e2.body) : (let' e1 e2).LC :=
  LC.let' h.choose e1_lc h.choose_spec

omit [HasFresh Var] [DecidableEq Var] in
lemma Term.body_from_lc_let (e1 e2 : Term Var) (let_lc : (let' e1 e2).LC) : e2.body := by
  cases let_lc with | let' L => exists L

omit [HasFresh Var] in
lemma Term.lc_case_from_body (e1 e2 e3 : Term Var) (e1_lc : e1.LC) (h₁ : e2.body) (h₂ : e3.body) :
    (case e1 e2 e3).LC := by
  cases h₁
  cases h₂
  apply LC.case (free_union Var) e1_lc <;> grind

omit [HasFresh Var] in
lemma Term.body_inl_from_lc_case (e1 e2 e3 : Term Var) (lc : (case e1 e2 e3).LC) : e2.body := by
  cases lc
  exists (free_union Var)
  grind

omit [HasFresh Var] in
lemma Term.body_inr_from_lc_case (e1 e2 e3 : Term Var) (lc : (case e1 e2 e3).LC) : e3.body := by
  cases lc
  exists (free_union Var)
  grind

lemma Term.open_tm_body (e1 e2 : Term Var) (h : e1.body) (e2_lc : e2.LC) : (e1 ^ᵗᵗ e2).LC := by
  cases h
  let ⟨x, _⟩ := fresh_exists <| free_union [fv_tm, fv_ty] Var
  grind [open_subst_intro_tm, subst_tm_lc]

namespace Ty.wf

omit [HasFresh Var] in
lemma LC (E : Env Var) (T : Ty Var) (T_wf : T.wf E) : T.LC := by
  induction T_wf
  case all L _ _ _ _ => 
    -- TODO: how to get grind to do this???
    apply LC.all L <;> grind
  all_goals grind [LC.top, LC.var, LC.arrow, LC.sum]

open List in
lemma weaken (T : Ty Var) (E F G) (wf_GE : T.wf (G ++ E)) (ok_GFE : (G ++ F ++ E)✓) :
    T.wf (G ++ F ++ E) := by
  generalize eq : G ++ E = F at wf_GE
  induction wf_GE generalizing G 
  case all => sorry
  case var F' _ X T mem => 
    subst eq
    have ok_GE : (G ++ E).NodupKeys := by apply NodupKeys.sublist (l₂ := G ++ F' ++ E) <;> grind
    have mem_weak : Binding.sub T ∈ (G ++ F' ++ E)[X]? := 
      sublist_dlookup (G ++ E) (G ++ F' ++ E) ok_GE ok_GFE (by grind) mem
    exact Ty.wf.var mem_weak
  all_goals grind

lemma weakening_head (T : Ty Var) (E F) (wf_E : T.wf E) (ok_FE : (F ++ E)✓) : T.wf (F ++ E) := by
  have : F ++ E = [] ++ F ++ E := by simp
  rw [this] at *
  grind [Ty.wf.weaken] 

-- TODO: I think a cons with Perm would be fine here

lemma narrow V U (T : Ty Var) E F X
  (wf : T.wf (F ++ [⟨X, Binding.sub V⟩] ++ E)) 
  (ok : (F ++ [⟨X, Binding.sub U⟩] ++ E)✓)
  : T.wf (F ++ [⟨X, Binding.sub U⟩] ++ E) := by
  generalize eq' : F ++ [⟨X, Binding.sub V⟩] ++ E = G' at wf
  generalize eq  : F ++ [⟨X, Binding.sub U⟩] ++ E = G  at wf
  induction wf generalizing F
  case var => sorry
  case all => sorry
  all_goals grind

lemma strengthen E F x U (T : Ty Var) (wf : T.wf (F ++ [⟨x, Binding.ty U⟩] ++ E)) : 
    T.wf (F ++ E) := by
  generalize eq : (F ++ [⟨x, Binding.ty U⟩] ++ E) = G at wf
  induction wf generalizing F
  case var => sorry
  case all => sorry
  all_goals grind

-- TODO: formatting...
lemma lc_subst (F : Env Var) Q (E : Env Var) Z (P T : Ty Var)
  (wf₁ : T.wf (F ++ [⟨Z, Binding.sub Q⟩] ++ E))
  (wf₂ : P.wf E)
  (ok : ((F ++ E).map (fun ⟨x, σ⟩ => (⟨x, σ[Z:=P]⟩ : ((_ : Var) × Binding Var))))✓)
  : T[Z := P].wf ((F ++ E).map (fun ⟨x, σ⟩ => (⟨x, σ[Z:=P]⟩ : ((_ : Var) × Binding Var))))
  := sorry

lemma open_ty E (U T1 T2 : Ty Var) (ok : E✓) (wf₁ : (Ty.all T1 T2).wf E) (wf₂ : U.wf E) : 
    (T2 ^ᵞ U).wf E := by
  cases wf₁ with | all L T1_wf cofin =>
  let ⟨x,_⟩ := fresh_exists <| free_union [fv] Var
  rw [open_subst_intro x]
  sorry
  grind

end Ty.wf

open Context

omit [HasFresh Var] in
lemma ok_from_wf_env (E : Env Var) (wf : E.wf) : E✓ := by
  induction wf 
  <;> constructor
  <;> first | assumption | grind [List.append_eq]

lemma wf_typ_from_binds_typ (x : Var) (U : Ty Var) (E : Env Var) (wf : E.wf) (bind : Binding.ty U ∈ E[x]?) :
    U.wf E := sorry

omit [HasFresh Var] in
lemma wf_typ_from_wf_env_typ (x : Var) (T : Ty Var) (E : Env Var)
    (wf : Env.wf ([⟨x, Binding.ty T⟩] ++ E)) : T.wf E := by
  cases wf
  assumption

omit [HasFresh Var] in
lemma wf_typ_from_wf_env_sub (x : Var) (T : Ty Var) (E : Env Var)
    (wf : Env.wf ([⟨x, Binding.sub T⟩] ++ E)) : T.wf E := by
  cases wf
  assumption

lemma wf_env_narrowing (V : Ty Var) (E : Env Var) F (U : Ty Var) X
  (wf_e : Env.wf (F ++ [⟨X, Binding.sub V⟩] ++ E)) 
  (wf_t : U.wf E) : Env.wf (F ++ [⟨X, Binding.sub U⟩] ++ E) := by
  induction F generalizing U X wf_t
  case nil =>
    cases wf_e
    -- TODO: grind this?
    constructor <;> assumption
  case cons => sorry

lemma wf_env_strengthening x (T : Ty Var) (E F : Env Var) (wf : Env.wf (F ++ [⟨x, Binding.ty T⟩] ++ E)) :
    (F ++ E).wf := by
  induction F generalizing E
  case nil =>
    cases wf
    grind
  case cons hd tl ih =>
    cases wf
    -- TODO : wait until we remove some appends to clean this up
    case sub h _ _ =>
      constructor
      · exact ih E h
      · grind [List.append_eq, Ty.wf.strengthen]
      · sorry
    case ty =>
      constructor
      · grind [List.append_eq]
      · grind [List.append_eq, Ty.wf.strengthen]
      · sorry

lemma wf_env_subst_tb Q Z (P : Ty Var) E F 
  (wf_e : Env.wf (F ++ [⟨Z, Binding.sub Q⟩] ++ E))
  (wf_t : P.wf E)
  : Env.wf ((F ++ E).map (fun ⟨x, σ⟩ => (⟨x, σ[Z:=P]⟩ : ((_ : Var) × Binding Var))))
  := sorry

lemma notin_fv_tt_open (Y X : Var) (T : Ty Var) (nmem : X ∉ (T ^ᵞ fvar Y).fv) : X ∉ T.fv := by
  induction T
  case all => sorry
  all_goals grind

lemma notin_fv_wf (E : Env Var) (X : Var) (T : Ty Var) (wf : T.wf E) (nmem : X ∉ E.dom) : 
    X ∉ T.fv := by
  induction wf
  case all => sorry
  all_goals grind

lemma map_subst_tb_id (G : Env Var) (Z : Var) (P : Ty Var) (wf : G.wf) (nmem : Z ∉ G.dom) :
    G = G.map (fun ⟨x, σ⟩ => (⟨x, σ[Z:=P]⟩ : ((_ : Var) × Binding Var))) := by
  induction wf
  case empty => grind
  case sub E _ T _ wf _ ih =>
    have Z_nmem_E_dom : Z ∉ E.dom := by
       simp_all only [dom, List.cons_append, List.nil_append, Function.comp_apply, List.keys_cons,
         List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, not_or]
       exact not_false        
    rw [ih Z_nmem_E_dom]
    simp only [List.cons_append, List.nil_append, List.map_cons, List.map_map, List.cons.injEq,
      Sigma.mk.injEq, heq_eq_eq, true_and, List.map_inj_left, Function.comp_apply]
    constructor
    · simp only [Binding.subst_sub]
      apply congrArg
      apply Ty.subst_fresh
      apply notin_fv_wf _ _ _ wf Z_nmem_E_dom
    · sorry
  case ty => sorry    

lemma sub_regular (E : Env Var) (S T : Ty Var) (sub : Sub E S T) : E.wf ∧ S.wf E ∧ T.wf E := sorry

lemma typing_regular (E : Env Var) (e : Term Var) (T : Ty Var) (der : Typing E e T) :
    E.wf ∧ e.LC ∧ T.wf E := sorry

lemma value_regular (e : Term Var) (val : Value e) : e.LC := by
  induction val <;> grind [LC.inl, LC.inr]

lemma red_regular (e e' : Term Var) (step : Red e e') : e.LC ∧ e'.LC := 
  sorry

end LambdaCalculus.LocallyNameless.Fsub
