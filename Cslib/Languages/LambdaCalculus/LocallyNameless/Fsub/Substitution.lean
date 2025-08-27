/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Basic
import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Opening


/-! # λ-calculus

The λ-calculus with polymorphism and subtyping, with a locally nameless representation of syntax.
This file defines substitution on types and terms.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is adapted

-/

universe u

variable {Var : Type u} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless.Fsub

namespace Ty

/-- Type substitution. -/
@[scoped grind =]
def subst (X : Var) (δ : Ty Var) : Ty Var → Ty Var
| top => top
| bvar J => bvar J
| fvar Y => if Y = X then δ else fvar Y
| arrow σ τ => arrow (subst X δ σ) (subst X δ τ)
| all σ τ => all (subst X δ σ) (subst X δ τ)
| sum σ τ => sum (subst X δ σ) (subst X δ τ)

instance : HasSubstitution (Ty Var) Var (Ty Var) where
  subst γ X δ := Ty.subst X δ γ

variable {σ τ δ γ : Ty Var}

@[scoped grind _=_]
lemma subst_def : Ty.subst (X : Var) (δ : Ty Var) (γ : Ty Var) = γ[X := δ] := by rfl

/-- Substitution of a free variable not present in a type leaves it unchanged. -/
@[scoped grind <=]
lemma subst_fresh (nmem : X ∉ γ.fv) (δ : Ty Var) : γ = γ[X := δ] := by
  induction γ <;> grind

variable [HasFresh Var]

/-- Substitution of a locally closed type distributes with opening. -/
@[scoped grind]
lemma openRec_subst (Y : ℕ) (σ τ : Ty Var) (lc : δ.LC) (X : Var) : 
    (σ⟦Y ↝ τ⟧ᵞ)[X := δ] = σ[X := δ]⟦Y ↝ τ[X := δ]⟧ᵞ := by
  induction σ generalizing Y
  all_goals grind

/-- Specialize `Ty.openRec_subst` to the first opening. -/
lemma open_subst (σ τ : Ty Var) (lc : δ.LC) (X : Var) : (σ ^ᵞ τ)[X := δ] = σ[X := δ] ^ᵞ τ[X := δ]
  := openRec_subst 0 σ τ lc X

/-- Specialize `Ty.subst_open` to free variables. -/
lemma open_subst_var (σ : Ty Var) (neq : Y ≠ X) (lc : δ.LC) :
    (σ ^ᵞ fvar Y)[X := δ] = (σ[X := δ]) ^ᵞ fvar Y := by grind

omit [HasFresh Var]

/-- Opening to a type is equivalent to opening to a free variable and substituting. -/
@[scoped grind]
lemma openRec_subst_intro (Y : ℕ) (δ : Ty Var) (nmem : X ∉ γ.fv) :
    γ⟦Y ↝ δ⟧ᵞ = (γ⟦Y ↝ fvar X⟧ᵞ)[X := δ] := by
  induction γ generalizing δ Y <;> grind

/-- Specialize `Ty.openRec_subst_intro` to the first opening. -/
lemma open_subst_intro (δ : Ty Var) (nmem : X ∉ γ.fv) : γ ^ᵞ δ = (γ ^ᵞ fvar X)[X := δ] := 
  openRec_subst_intro _ _ nmem

variable [HasFresh Var]

@[scoped grind =>]
lemma subst_lc (σ_lc : σ.LC) (τ_lc : τ.LC) (X : Var) : σ[X := τ].LC := by
  induction σ_lc
  case all => apply LC.all (free_union Var) <;> grind
  all_goals grind 

end Ty

namespace Term

open scoped Ty

/-- Substitution of a type within a term. -/
@[scoped grind =]
def subst_ty (X : Var) (δ : Ty Var) : Term Var → Term Var
| bvar x => bvar x
| fvar x => fvar x
| abs σ t₁ => abs (σ [X := δ]) (subst_ty X δ t₁)
| app t₁ t₂ => app (subst_ty X δ t₁) (subst_ty X δ t₂)
| tabs σ t₁ => tabs (σ [X := δ]) (subst_ty X δ t₁)
| tapp t₁ σ => tapp (subst_ty X δ t₁) (σ[X := δ])
| let' t₁ t₂ => let' (subst_ty X δ t₁) (subst_ty X δ t₂)
| inl t₁ => inl (subst_ty X δ t₁)
| inr t₁ => inr (subst_ty X δ t₁)
| case t₁ t₂ t₃ => case (subst_ty X δ t₁) (subst_ty X δ t₂) (subst_ty X δ t₃)

instance : HasSubstitution (Term Var) Var (Ty Var) where
  subst t X δ := Term.subst_ty X δ t

@[scoped grind _=_]
lemma subst_ty_def : subst_ty (X : Var) (δ : Ty Var) (t : Term Var) = t[X := δ] := by rfl

variable {t : Term Var} {δ : Ty Var}

/-- Substitution of a free type variable not present in a term leaves it unchanged. -/
lemma subst_ty_fresh (nmem : X ∉ t.fv_ty) (δ : Ty Var) : t = t [X := δ] := 
  by induction t <;> grind

variable [HasFresh Var]

/-- Substitution of a locally closed type distributes with term opening to a type . -/
@[scoped grind]
lemma openRec_ty_subst_ty (Y : ℕ) (t : Term Var) (σ : Ty Var) (lc : δ.LC) (X : Var) : 
    (t⟦Y ↝ σ⟧ᵗᵞ)[X := δ] = (t[X := δ])⟦Y ↝  σ[X := δ]⟧ᵗᵞ := by
  induction t generalizing Y <;> grind

/-- Specialize `Term.openRec_ty_subst` to the first opening. -/
lemma open_ty_subst_ty (t : Term Var) (σ : Ty Var) (lc : δ.LC) (X : Var) :
     (t ^ᵗᵞ σ)[X := δ] = t[X := δ] ^ᵗᵞ σ[X := δ] := openRec_ty_subst_ty 0 t σ lc X

/-- Specialize `Term.open_ty_subst` to free type variables. -/
lemma open_ty_subst_ty_var (t : Term Var) (neq : Y ≠ X) (lc : δ.LC) :
    (t ^ᵗᵞ .fvar Y)[X := δ] = t[X := δ] ^ᵗᵞ .fvar Y := by grind

omit [HasFresh Var]

/-- Opening a term to a type is equivalent to opening to a free variable and substituting. -/
lemma openRec_ty_subst_ty_intro (Y : ℕ) (t : Term Var) (nmem : X ∉ t.fv_ty) : 
  t⟦Y ↝ δ⟧ᵗᵞ = (t⟦Y ↝ Ty.fvar X⟧ᵗᵞ)[X := δ] := by
  induction t generalizing X δ Y <;> grind

/-- Specialize `Term.openRec_ty_subst_ty_intro` to the first opening. -/
lemma open_ty_subst_ty_intro (t : Term Var) (δ : Ty Var) (nmem : X ∉ t.fv_ty) : 
    t ^ᵗᵞ δ = (t ^ᵗᵞ Ty.fvar X)[X := δ] := openRec_ty_subst_ty_intro _ _ nmem

/-- Substitution of a term within a term. -/
@[scoped grind =]
def subst_tm (x : Var) (s : Term Var) : Term Var → Term Var
| bvar x => bvar x
| fvar y => if y = x then s else fvar y
| abs σ t₁ => abs σ (subst_tm x s t₁)
| app t₁ t₂ => app (subst_tm x s t₁) (subst_tm x s t₂)
| tabs σ t₁ => tabs σ (subst_tm x s t₁)
| tapp t₁ σ => tapp (subst_tm x s t₁) σ
| let' t₁ t₂ => let' (subst_tm x s t₁) (subst_tm x s t₂)
| inl t₁ => inl (subst_tm x s t₁)
| inr t₁ => inr (subst_tm x s t₁)
| case t₁ t₂ t₃ => case (subst_tm x s t₁) (subst_tm x s t₂) (subst_tm x s t₃)

instance : HasSubstitution (Term Var) Var (Term Var) where
  subst t x s := Term.subst_tm x s t

@[scoped grind _=_]
lemma subst_tm_def : subst_tm (x : Var) (s : Term Var) (t : Term Var) = t[x := s] := by rfl

variable {t s : Term Var} {δ : Ty Var} {x : Var}

/-- Substitution of a free term variable not present in a term leaves it unchanged. -/
lemma subst_tm_fresh (nmem : x ∉ t.fv_tm) (s : Term Var) : t = t[x := s] := by
  induction t <;> grind

variable [HasFresh Var]

/-- Substitution of a locally closed term distributes with term opening to a term. -/
lemma openRec_tm_subst_tm (y : ℕ) (t₁ t₂ : Term Var) (lc : s.LC) (x : Var) :
    (t₁⟦y ↝ t₂⟧ᵗᵗ)[x := s] = (t₁[x := s])⟦y ↝  t₂[x := s]⟧ᵗᵗ := by
  induction t₁ generalizing y <;> grind

/-- Specialize `Term.openRec_tm_subst_tm` to the first opening. -/
lemma open_tm_subst_tm (t₁ t₂ : Term Var) (lc : s.LC) (x : Var) :
    (t₁ ^ᵗᵗ t₂)[x := s] = (t₁[x := s]) ^ᵗᵗ t₂[x := s] := openRec_tm_subst_tm 0 t₁ t₂ lc x

/-- Specialize `Term.openRec_tm_subst_tm` to free term variables. -/ 
lemma open_tm_subst_tm_var (t : Term Var) (neq : y ≠ x) (lc : s.LC) :
     (t ^ᵗᵗ fvar y)[x := s] = (t[x := s]) ^ᵗᵗ fvar y := by grind [open_tm_subst_tm]

omit [HasFresh Var]

/-- Substitution of a locally closed type distributes with term opening to a term. -/
lemma openRec_tm_subst_ty (y : ℕ) (t₁ t₂ : Term Var) (δ : Ty Var) (X : Var) :
    (t₁⟦y ↝ t₂⟧ᵗᵗ)[X := δ] = (t₁[X := δ])⟦y ↝  t₂[X := δ]⟧ᵗᵗ := by
  induction t₁ generalizing y <;> grind

/-- Specialize `Term.openRec_tm_subst_ty` to the first opening -/
lemma open_tm_subst_ty (t₁ t₂ : Term Var) (δ : Ty Var) (X : Var) :
    (t₁ ^ᵗᵗ t₂)[X := δ] = (t₁[X := δ]) ^ᵗᵗ t₂[X := δ] := openRec_tm_subst_ty 0 t₁ t₂ δ X

/-- Specialize `Term.open_tm_subst_ty` to free term variables -/
lemma open_tm_subst_ty_var (t₁ : Term Var) (δ : Ty Var) (X y : Var) :
    (t₁ ^ᵗᵗ fvar y)[X := δ] = (t₁[X := δ]) ^ᵗᵗ fvar y := by grind [open_tm_subst_ty]

variable [HasFresh Var]

/-- Substitution of a locally closed term distributes with term opening to a type. -/
lemma openRec_ty_subst_tm (Y : ℕ) (t : Term Var) (δ : Ty Var) (lc : s.LC) (x : Var) :
    (t⟦Y ↝ δ⟧ᵗᵞ)[x := s] = t[x := s]⟦Y ↝ δ⟧ᵗᵞ := by
  induction t generalizing Y <;> grind

/-- Specialize `Term.openRec_ty_subst_tm` to the first opening. -/
lemma open_ty_subst_tm (t : Term Var) (δ : Ty Var) (lc : s.LC) (x : Var) :
    (t ^ᵗᵞ δ)[x := s] = t[x := s] ^ᵗᵞ δ := openRec_ty_subst_tm 0 t δ lc x

/-- Specialize `Term.open_ty_subst_tm` to free type variables. -/
lemma open_ty_subst_tm_var (t : Term Var) (lc : s.LC) (x Y : Var) :
    (t ^ᵗᵞ .fvar Y)[x := s] = t[x := s] ^ᵗᵞ .fvar Y := open_ty_subst_tm _ _ lc _

omit [HasFresh Var]

/-- Opening a term to a term is equivalent to opening to a free variable and substituting. -/
lemma openRec_tm_subst_tm_intro (y : ℕ) (t s : Term Var) (nmem : x ∉ t.fv_tm) :
    t⟦y ↝ s⟧ᵗᵗ = (t⟦y ↝ fvar x⟧ᵗᵗ)[x := s] := by
  induction t generalizing y <;> grind

/-- Specialize `Term.openRec_tm_subst_tm_intro` to the first opening. -/
lemma open_tm_subst_tm_intro (t s : Term Var) (nmem : x ∉ t.fv_tm) :
    t ^ᵗᵗs = (t ^ᵗᵗ fvar x)[x := s] := openRec_tm_subst_tm_intro _ _ _ nmem

variable [HasFresh Var]

lemma subst_ty_lc (t_lc : t.LC) (δ_lc : δ.LC) (X : Var) : t[X := δ].LC := by
  induction t_lc
  case abs | tabs | let' | case => sorry
  all_goals grind

lemma subst_tm_lc (t_lc : t.LC) (s_lc : s.LC) (x : Var) : t[x := s].LC := by
  induction t_lc
  case abs | tabs | let' | case => sorry
  all_goals grind

end Term

namespace Binding

/-- Binding substitution of types. -/
@[scoped grind =]
def subst (X : Var) (δ : Ty Var) : Binding Var → Binding Var
| sub γ => sub <| γ[X := δ]
| ty  γ => ty  <| γ[X := δ]

instance : HasSubstitution (Binding Var) Var (Ty Var) where
  subst γ X δ := Binding.subst X δ γ

variable {δ γ : Ty Var} {X : Var}

@[scoped grind _=_]
lemma subst_sub : (sub γ)[X := δ] = sub (γ[X := δ]) := by rfl

@[scoped grind _=_]
lemma subst_ty : (ty γ)[X := δ] = ty (γ[X := δ]) := by rfl

end Binding

end LambdaCalculus.LocallyNameless.Fsub
