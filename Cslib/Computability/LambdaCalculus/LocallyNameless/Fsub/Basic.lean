/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Data.HasFresh
import Cslib.Syntax.HasSubstitution
import Cslib.Computability.LambdaCalculus.LocallyNameless.Context

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

/-- Types of the polymorphic lambda calculus. -/
inductive Ty (Var : Type u)
  /-- The type ⊤, with a single inhabitant. -/
  | top : Ty Var
  /-- Bound variables that appear in a type, using a de-Bruijn index. -/
  | bvar : ℕ → Ty Var
  /-- Free type variables. -/
  | fvar : Var → Ty Var
  /-- A function type. -/
  | arrow : Ty Var → Ty Var → Ty Var
  /-- A universal quantification. -/
  | all : Ty Var → Ty Var → Ty Var
  /-- A sum type. -/
  | sum : Ty Var → Ty Var → Ty Var
  deriving Inhabited

/-- Syntax of locally nameless lambda terms, with free variables over `Var`. -/
inductive Term (Var : Type u)
  /-- Bound term variables that appear under a lambda abstraction, using a de-Bruijn index. -/
  | bvar : ℕ → Term Var
  /-- Free term variables. -/
  | fvar : Var → Term Var
  /-- Lambda abstraction, introducing a new bound term variable. -/
  | abs : Ty Var → Term Var → Term Var
  /-- Function application. -/
  | app : Term Var → Term Var → Term Var
  /-- Type abstraction, introducing a new bound type variable. -/
  | tabs : Ty Var → Term Var → Term Var
  /-- Type application. -/
  | tapp : Term Var → Ty Var → Term Var
  /-- Binding of a term. -/
  | let' : Term Var → Term Var → Term Var
  /-- Left constructor of a sum. -/
  | inl : Term Var → Term Var
  /-- Right constructor of a sum. -/
  | inr : Term Var → Term Var
  /-- Case matching on a sum. -/
  | case : Term Var → Term Var → Term Var → Term Var

/-- Variable opening (type opening to type) of the ith bound variable. -/
@[scoped grind =]
def Ty.openRec (K : ℕ) (U : Ty Var) : Ty Var → Ty Var
| top => top
| bvar J => if K = J then U else bvar J
| fvar X => fvar X
| arrow T1 T2 => arrow (openRec K U T1) (openRec K U T2)
| all T1 T2 => all (openRec K U T1) (openRec (K + 1) U T2)
| sum T1 T2 => sum (openRec K U T1) (openRec K U T2)

scoped notation:68 e "⟦" i " ↝ " sub "⟧ᵞ"=> Ty.openRec i sub e

lemma Ty.openRec_top : top⟦i ↝ s⟧ᵞ = top := by rfl

lemma Ty.openRec_bvar : (bvar i')⟦i ↝ s⟧ᵞ = if i = i' then s else (bvar i') := by rfl

lemma Ty.openRec_fvar : (fvar x)⟦i ↝ s⟧ᵞ = fvar x := by rfl

lemma Ty.openRec_arrow : (arrow T1 T2)⟦i ↝ s⟧ᵞ = arrow (T1⟦i ↝ s⟧ᵞ) (T2⟦i ↝ s⟧ᵞ) := by rfl

lemma Ty.openRec_all : (all T1 T2)⟦i ↝ s⟧ᵞ = all (T1⟦i ↝ s⟧ᵞ) (T2⟦i + 1 ↝ s⟧ᵞ) := by rfl

lemma Ty.openRec_sum : (sum T1 T2)⟦i ↝ s⟧ᵞ = sum (T1⟦i ↝ s⟧ᵞ) (T2⟦i ↝ s⟧ᵞ) := by rfl

/-- Variable opening (type opening to type) of the closest binding. -/
@[scoped grind =]
def Ty.open' (T U : Ty Var) := Ty.openRec 0 U T

scoped infixr:80 " ^ᵞ " => Ty.open'

theorem Ty.open'_eq : e ^ᵞ s = e⟦0 ↝ s⟧ᵞ := by rfl

/-- Variable opening (term opening to type) of the ith bound variable. -/
@[scoped grind =]
def Term.openRec_ty (K : ℕ) (U : Ty Var) : Term Var → Term Var
| bvar i => bvar i
| fvar x => fvar x
| abs V e1 => abs (V⟦K ↝ U⟧ᵞ) (openRec_ty K U e1)
| app e1 e2 => app (openRec_ty K U e1) (openRec_ty K U e2)
| tabs V e1 => tabs (V⟦K ↝ U⟧ᵞ) (openRec_ty (K + 1) U e1)
| tapp e1 V => tapp (openRec_ty K U e1) (V⟦K ↝ U⟧ᵞ)
| let' e1 e2 => let' (openRec_ty K U e1) (openRec_ty K U e2)
| inl e1 => inl (openRec_ty K U e1)
| inr e2 => inr (openRec_ty K U e2)
| case e1 e2 e3 =>
    case (openRec_ty K U e1) (openRec_ty K U e2) (openRec_ty K U e3)

scoped notation:68 e "⟦" i " ↝ " sub "⟧ᵗᵞ"=> Term.openRec_ty i sub e

lemma Term.openRec_ty_bvar : (bvar i)⟦i ↝ s⟧ᵗᵞ = bvar i := by rfl

lemma Term.openRec_ty_fvar : (fvar x)⟦i ↝ s⟧ᵗᵞ = fvar x := by rfl

lemma Term.openRec_ty_abs : (abs V e1)⟦i ↝ s⟧ᵗᵞ = abs (V⟦i ↝ s⟧ᵞ) (e1⟦i ↝ s⟧ᵗᵞ) := by rfl

lemma Term.openRec_ty_app : (app e1 e2)⟦i ↝ s⟧ᵗᵞ = app (e1⟦i ↝ s⟧ᵗᵞ) (e2⟦i ↝ s⟧ᵗᵞ) := by rfl

lemma Term.openRec_ty_tabs : (tabs V e1)⟦i ↝ s⟧ᵗᵞ = tabs (V⟦i ↝ s⟧ᵞ) (e1⟦i + 1 ↝ s⟧ᵗᵞ) := by rfl

lemma Term.openRec_ty_tapp : (tapp e1 V)⟦i ↝ s⟧ᵗᵞ = tapp (e1⟦i ↝ s⟧ᵗᵞ) (V⟦i ↝ s⟧ᵞ) := by rfl

lemma Term.openRec_ty_let' : (let' e1 e2)⟦i ↝ s⟧ᵗᵞ = let' (e1⟦i ↝ s⟧ᵗᵞ) (e2⟦i ↝ s⟧ᵗᵞ) := by rfl

lemma Term.openRec_ty_inl : (inl e1)⟦i ↝ s⟧ᵗᵞ = inl (e1⟦i ↝ s⟧ᵗᵞ) := by rfl

lemma Term.openRec_ty_inr : (inr e1)⟦i ↝ s⟧ᵗᵞ = inr (e1⟦i ↝ s⟧ᵗᵞ) := by rfl

lemma Term.openRec_ty_case : 
    (case e1 e2 e3)⟦i ↝ s⟧ᵗᵞ = case (e1⟦i ↝ s⟧ᵗᵞ) (e2⟦i ↝ s⟧ᵗᵞ) (e3⟦i ↝ s⟧ᵗᵞ) := by rfl

/-- Variable opening (term opening to type) of the closest binding. -/
@[scoped grind =]
def Term.open_ty (e : Term Var) U := Term.openRec_ty 0 U e

scoped infixr:80 " ^ᵗᵞ " => Term.open_ty

omit [HasFresh Var] [DecidableEq Var] in
theorem Term.open_ty_eq {e : Term Var} : e ^ᵗᵞ s = e⟦0 ↝ s⟧ᵗᵞ := by rfl

/-- Variable opening (term opening to term) of the ith bound variable. -/
@[scoped grind =]
def Term.openRec_tm (k : ℕ) (f : Term Var) (e : Term Var) : Term Var :=
  match e with
  | bvar i => if k = i then f else (bvar i)
  | fvar x => fvar x
  | abs V e1 => abs V (openRec_tm (k + 1) f e1)
  | app e1 e2 => app (openRec_tm k f e1) (openRec_tm k f e2)
  | tabs V e1 => tabs V (openRec_tm k f e1)
  | tapp e1 V => tapp (openRec_tm k f e1) V
  | let' e1 e2 => let' (openRec_tm k f e1) (openRec_tm (k + 1) f e2)
  | inl e1 => inl (openRec_tm k f e1)
  | inr e2 => inr (openRec_tm k f e2)
  | case e1 e2 e3 =>
      case (openRec_tm k f e1)
               (openRec_tm (k + 1) f e2)
               (openRec_tm (k + 1) f e3)

scoped notation:68 e "⟦" i " ↝ " sub "⟧ᵗᵗ"=> Term.openRec_tm i sub e

section

variable {s : Term Var}

omit [HasFresh Var] [DecidableEq Var]

lemma Term.openRec_tm_bvar : (bvar i')⟦i ↝ s⟧ᵗᵗ = if i = i' then s else (bvar i') := by rfl

lemma Term.openRec_tm_fvar : (fvar x)⟦i ↝ s⟧ᵗᵗ = fvar x := by rfl

lemma Term.openRec_tm_abs : (abs V e1)⟦i ↝ s⟧ᵗᵗ = abs V (e1⟦i + 1 ↝ s⟧ᵗᵗ) := by rfl

lemma Term.openRec_tm_app : (app e1 e2)⟦i ↝ s⟧ᵗᵗ = app (e1⟦i ↝ s⟧ᵗᵗ) (e2⟦i ↝ s⟧ᵗᵗ) := by rfl

lemma Term.openRec_tm_tabs : (tabs V e1)⟦i ↝ s⟧ᵗᵗ = tabs V (e1⟦i ↝ s⟧ᵗᵗ) := by rfl

lemma Term.openRec_tm_tapp : (tapp e1 V)⟦i ↝ s⟧ᵗᵗ = tapp (e1⟦i ↝ s⟧ᵗᵗ) V := by rfl

lemma Term.openRec_tm_let' : (let' e1 e2)⟦i ↝ s⟧ᵗᵗ = let' (e1⟦i ↝ s⟧ᵗᵗ) (e2⟦i + 1 ↝ s⟧ᵗᵗ) := by rfl

lemma Term.openRec_tm_inl : (inl e1)⟦i ↝ s⟧ᵗᵗ = inl (e1⟦i ↝ s⟧ᵗᵗ) := by rfl

lemma Term.openRec_tm_inr : (inr e1)⟦i ↝ s⟧ᵗᵗ = inr (e1⟦i ↝ s⟧ᵗᵗ) := by rfl

lemma Term.openRec_tm_case : 
    (case e1 e2 e3)⟦i ↝ s⟧ᵗᵗ = case (e1⟦i ↝ s⟧ᵗᵗ) (e2⟦i +1 ↝ s⟧ᵗᵗ) (e3⟦i + 1 ↝ s⟧ᵗᵗ) := by rfl

end

/-- Variable opening (term opening to term) of the closest binding. -/
@[scoped grind =]
def Term.open_tm (e1 e2 : Term Var) := Term.openRec_tm 0 e2 e1

scoped infixr:80 " ^ᵗᵗ " => Term.open_tm

/-- Locally closed types. -/
@[scoped grind cases]
inductive Ty.LC : Ty Var → Prop
  | top : LC top
  | var : LC (fvar X)
  | arrow : LC T1 → LC T2 → LC (arrow T1 T2)
  | all (L : Finset Var) : LC T1 → (∀ X ∉ L, LC (T2 ^ᵞ fvar X)) → LC (all T1 T2)
  | sum :LC T1 → LC T2 → LC (sum T1 T2)

/-- Locally closed terms. -/
@[scoped grind cases]
inductive Term.LC : Term Var → Prop
  | var : LC (fvar x)
  | abs (L : Finset Var) : T.LC → (∀ x ∉ L, LC (e1 ^ᵗᵗ fvar x)) → LC (abs T e1)
  | app : LC e1 → LC e2 → LC (app e1 e2)
  | tabs (L : Finset Var) : T.LC → (∀ X ∉ L, LC (e1 ^ᵗᵞ Ty.fvar X)) → LC (tabs T e1)
  | tapp : LC e1 → V.LC → LC (tapp e1 V)
  | let' (L : Finset Var) : LC e1 → (∀ x ∉ L, LC (e2 ^ᵗᵗ fvar x)) → LC (let' e1 e2)
  | inl : LC e1 → LC (inl e1)
  | inr : LC e1 → LC (inr e1)
  | case (L : Finset Var) :
      LC e1 →
      (∀ x ∉ L, LC (e2 ^ᵗᵗ fvar x)) →
      (∀ x ∉ L, LC (e3 ^ᵗᵗ fvar x)) →
      LC (case e1 e2 e3)

/-- Existential predicate for being a locally closed body of an abstraction. -/
@[scoped grind =]
def Term.body (e : Term Var) := ∃ L : Finset Var, ∀ x ∉ L, LC (e ^ᵗᵗ Term.fvar x)

/-- A context binding. -/
inductive Binding (Var : Type u) : Type (u + 1)
  /-- Subtype binding. -/
  | sub : Ty Var → Binding Var
  /-- Type binding. -/
  | ty : Ty Var → Binding Var
  deriving Inhabited

/-- A context of bindings. -/
abbrev Env (Var : Type u) := Context Var (Binding Var)

/-- A type is well-formed when it is locally closed and all free variables appear in a context. -/
inductive Ty.wf : Env Var → Ty Var → Prop
  | top : wf E top
  | var : Binding.sub U ∈ E[X]? → wf E (fvar X)
  | arrow : wf E T1 → wf E T2 → wf E (arrow T1 T2)
  | all (L : Finset Var) : 
      wf E T1 →
      (∀ X ∉ L, wf ([⟨X,Binding.sub T1⟩] ++ E) (T2 ^ᵞ fvar X)) →
      wf E (all T1 T2)
  | sum : wf E T1 → wf E T2 → wf E (sum T1 T2)

attribute [scoped grind] Ty.wf.top Ty.wf.var Ty.wf.arrow Ty.wf.sum

/-- An environment is well-formed if it binds each variable exactly once to a well-formed type. -/
inductive Env.wf : Env Var → Prop
  | empty : wf []
  | sub : wf E → T.wf E → X ∉ E.dom → wf ([⟨X, Binding.sub T⟩] ++ E)
  | ty : wf E → T.wf E → x ∉ E.dom → wf ([⟨x, Binding.ty T⟩] ++ E)

/-- The subtyping relation. -/
inductive Ty.Sub : Env Var → Ty Var → Ty Var → Prop
  | top : E.wf → S.wf E → Sub E S top
  | refl_tvar : E.wf → (fvar X).wf E → Sub E (fvar X) (fvar X)
  | trans_tvar : Binding.sub U ∈ E[X]? → Sub E U T → Sub E (fvar X) T
  | arrow : Sub E T1 S1 → Sub E S2 T2 → Sub E (arrow S1 S2) (arrow T1 T2)
  | all (L : Finset Var) :
      Sub E T1 S1 →
      (∀ X ∉ L, Sub ([⟨X, Binding.sub T1⟩] ++ E) (S2 ^ᵞ fvar X) (T2 ^ᵞ fvar X)) →
      Sub E (all S1 S2) (all T1 T2)
  | sum : Sub E S1 T1 → Sub E S2 T2 → Sub E (sum S1 S2) (sum T1 T2)

open Term Ty in
/-- The typing relation. -/
inductive Typing : Env Var → Term Var → Ty Var → Prop
  | var : E.wf → Binding.ty T ∈ E[x]? → Typing E (fvar x) T
  | abs (L : Finset Var) :
      (∀ x ∉ L, Typing ([⟨x, Binding.ty V⟩] ++ E) (e1 ^ᵗᵗ fvar x) T1) →
      Typing E (abs V e1) (arrow V T1)
  | app : Typing E e1 (arrow T1 T2) → Typing E e2 T1 → Typing E (app e1 e2) T2
  | tabs (L : Finset Var) :
      (∀ X ∉ L, Typing ([⟨X, Binding.sub V⟩] ++ E) (e1 ^ᵗᵞ fvar X) (T1 ^ᵞ fvar X)) →
      Typing E (tabs V e1) (all V T1)
  | tapp : Typing E e1 (all T1 T2) → Sub E T T1 → Typing E (tapp e1 T) (T2 ^ᵞ T)
  | sub : Typing E e S → Sub E S T → Typing E e T
  | let' (L : Finset Var) :
      Typing E e1 T1 →
      (∀ x ∉ L, Typing ([⟨x, Binding.ty T1⟩] ++ E) (e2 ^ᵗᵗ fvar x) T2) →
      Typing E (let' e1 e2) T2
  | inl : Typing E e1 T1 → T2.wf E → Typing E (inl e1) (sum T1 T2)
  | inr : Typing E e1 T2 → T1.wf E → Typing E (inr e1) (sum T1 T2)
  | case (L : Finset Var) :
      Typing E e1 (sum T1 T2) →
      (∀ x ∉ L, Typing ([⟨x, Binding.ty T1⟩] ++ E) (e2 ^ᵗᵗ fvar x) T) →
      (∀ x ∉ L, Typing ([⟨x, Binding.ty T2⟩] ++ E) (e3 ^ᵗᵗ fvar x) T) →
      Typing E (case e1 e2 e3) T

/-- Values are irreducible terms. -/
inductive Term.Value : Term Var → Prop
  | abs : LC (abs T e1) → Value (abs T e1)
  | tabs : LC (tabs T e1) → Value (tabs T e1)
  | inl : Value e1 → Value (inl e1)
  | inr : Value e1 → Value (inr e1)

/-- The vall-by-value reduction relation. -/
inductive Term.Red : Term Var → Term Var → Prop
  | app_1 : LC e2 → Red e1 e1' → Red (app e1 e2) (app e1' e2)
  | app_2 : Value e1 → Red e2 e2' → Red (app e1 e2) (app e1 e2')
  | tapp : V.LC → Red e1 e1' → Red (tapp e1 V) (tapp e1' V)
  | abs : LC (abs T e1) → Value v2 → Red (app (abs T e1) v2) (e1 ^ᵗᵗ v2)
  | tabs : LC (tabs T1 e1) → T2.LC → Red (tapp (tabs T1 e1) T2) (e1 ^ᵗᵞ T2)
  | let_1 : Red e1 e1' → e2.body → Red (let' e1 e2) (let' e1' e2)
  | let' : Value v1 → e2.body → Red (let' v1 e2) (e2 ^ᵗᵗ v1)
  | inl_1 : Red e1 e1' → Red (inl e1) (inl e1')
  | inr_1 : Red e1 e1' → Red (inr e1) (inr e1')
  | case_1 : Red e1 e1' → e2.body → e3.body → Red (case e1 e2 e3) (case e1' e2 e3)
  | case_inl : Value v1 → e2.body → e3.body → Red (case (inl v1) e2 e3) (e2 ^ᵗᵗ v1)
  | case_inr : Value v1 → e2.body → e3.body → Red (case (inr v1) e2 e3) (e3 ^ᵗᵗ v1)


/-- Free variables of a type. -/
@[scoped grind =]
def Ty.fv : Ty Var → Finset Var
| top | bvar _ => {}
| fvar X => {X}
| arrow T1 T2 | all T1 T2 | sum T1 T2 => T1.fv ∪ T2.fv

/-- Free type variables of a term. -/
@[scoped grind =]
def Term.fv_ty : Term Var → Finset Var
| bvar _ | fvar _ => {}
| abs V e1 | tabs V e1 | tapp e1 V => V.fv ∪ e1.fv_ty
| app e1 e2 | let' e1 e2 => e1.fv_ty ∪ e2.fv_ty
| inl e1 | inr e1 => e1.fv_ty
| case e1 e2 e3 => e1.fv_ty ∪ e2.fv_ty ∪ e3.fv_ty

/-- Free term variables of a term. -/
@[scoped grind =]
def Term.fv_tm : Term Var → Finset Var
| bvar _ => {}
| fvar x => singleton x
| abs _ e1 | tabs _ e1 | tapp e1 _ => e1.fv_tm
| app e1 e2 | let' e1 e2 => e1.fv_tm ∪ e2.fv_tm
| inl e1 | inr e1 => e1.fv_tm
| case e1 e2 e3 => e1.fv_tm ∪ e2.fv_tm ∪ e3.fv_tm

/-- Type substitution. -/
@[scoped grind =]
def Ty.subst (Z : Var) (U : Ty Var) : Ty Var → Ty Var
| top => top
| bvar J => bvar J
| fvar X => if X = Z then U else fvar X
| arrow T1 T2 => arrow (subst Z U T1) (subst Z U T2)
| all T1 T2 => all (subst Z U T1) (subst Z U T2)
| sum T1 T2 => sum (subst Z U T1) (subst Z U T2)

instance : HasSubstitution (Ty Var) Var (Ty Var) where
  subst m x n := Ty.subst x n m

section

omit [HasFresh Var]

variable {x : Var} {n : Ty Var}

lemma Ty.subst_top : top[x := n] = (top : Ty Var) := by rfl

lemma Ty.subst_bvar : (bvar i : Ty Var)[x := n] = bvar i := by rfl

lemma Ty.subst_fvar : (fvar x')[x := n] = if x' = x then n else fvar x' := by rfl

lemma Ty.subst_arrow : (arrow T1 T2 : Ty Var)[x := n] = arrow (T1[x := n]) (T2[x := n]) := by rfl

lemma Ty.subst_all : (all T1 T2 : Ty Var)[x := n] = all (T1[x := n]) (T2[x := n]) := by rfl

lemma Ty.subst_sum : (sum T1 T2 : Ty Var)[x := n] = sum (T1[x := n]) (T2[x := n]) := by rfl

@[scoped grind _=_]
lemma Ty.subst_def : Ty.subst (x : Var) (n : Ty Var) (m : Ty Var) = m[x := n] := by rfl

end

/-- Term substitution of types. -/
@[scoped grind =]
def Term.subst_ty (Z : Var) (U : Ty Var) : Term Var → Term Var
| bvar i => bvar i
| fvar x => fvar x
| abs V e1 => abs (V [Z := U]) (subst_ty Z U e1)
| app e1 e2 => app (subst_ty Z U e1) (subst_ty Z U e2)
| tabs V e1 => tabs (V [Z := U]) (subst_ty Z U e1)
| tapp e1 V => tapp (subst_ty Z U e1) (V[Z := U])
| let' e1 e2 => let' (subst_ty Z U e1) (subst_ty Z U e2)
| inl e1 => inl (subst_ty Z U e1)
| inr e1 => inr (subst_ty Z U e1)
| case e1 e2 e3 => case (subst_ty Z U e1) (subst_ty Z U e2) (subst_ty Z U e3)

instance : HasSubstitution (Term Var) Var (Ty Var) where
  subst m x n := Term.subst_ty x n m
    
section

omit [HasFresh Var]

variable {x : Var} {n : Ty Var}

lemma Term.subst_ty_bvar : (bvar i : Term Var)[x := n] = bvar i := by rfl

lemma Term.subst_ty_fvar : (fvar x : Term Var)[x := n] = fvar x := by rfl

lemma Term.subst_ty_abs : (abs V e1 : Term Var)[x := n] = abs (V [x := n]) (e1[x := n]) := by rfl

lemma Term.subst_ty_app : (app e1 e2 : Term Var)[x := n] = app (e1[x := n]) (e2[x := n]) := by rfl

lemma Term.subst_ty_tabs : (tabs V e1 : Term Var)[x := n] = tabs (V [x := n]) (e1[x := n]) := by rfl

lemma Term.subst_ty_tapp : (tapp e1 V : Term Var)[x := n] = tapp (e1 [x := n]) (V[x := n]) := by rfl

lemma Term.subst_ty_let' : 
    (let' e1 e2 : Term Var)[x := n] = let' (e1 [x := n]) (e2[x := n]) := by rfl

lemma Term.subst_ty_inl : (inl e1 : Term Var)[x := n] = inl (e1[x := n]) := by rfl

lemma Term.subst_ty_inr : (inr e1 : Term Var)[x := n] = inr (e1[x := n]) := by rfl

lemma Term.subst_ty_case : 
    (case e1 e2 e3 : Term Var)[x := n] = case (e1[x := n]) (e2[x := n]) (e3[x := n]) := by rfl

@[scoped grind _=_]
lemma Term.subst_ty_def : Term.subst_ty (x : Var) (n : Ty Var) (m : Term Var) = m[x := n] := by rfl

end

/-- Term substitution of terms. -/
@[scoped grind =]
def Term.subst_tm (z : Var) (u : Term Var) : Term Var → Term Var
| bvar i => bvar i
| fvar x => if x = z then u else fvar x
| abs V e1 => abs V (subst_tm z u e1)
| app e1 e2 => app (subst_tm z u e1) (subst_tm z u e2)
| tabs V e1 => tabs V (subst_tm z u e1)
| tapp e1 V => tapp (subst_tm z u e1) V
| let' e1 e2 => let' (subst_tm z u e1) (subst_tm z u e2)
| inl e1 => inl (subst_tm z u e1)
| inr e1 => inr (subst_tm z u e1)
| case e1 e2 e3 => case (subst_tm z u e1) (subst_tm z u e2) (subst_tm z u e3)

instance : HasSubstitution (Term Var) Var (Term Var) where
  subst m x n := Term.subst_tm x n m

section

omit [HasFresh Var]

variable {x : Var} {n : Term Var}

lemma Term.subst_tm_bvar : (bvar i : Term Var)[x := n] = bvar i := by rfl

lemma Term.subst_tm_fvar : (fvar x' : Term Var)[x := n] = if x' = x then n else fvar x' := by rfl

lemma Term.subst_tm_abs : (abs V e1 : Term Var)[x := n] = abs V (e1[x := n]) := by rfl

lemma Term.subst_tm_app : (app e1 e2 : Term Var)[x := n] = app (e1[x := n]) (e2[x := n]) := by rfl

lemma Term.subst_tm_tabs : (tabs V e1 : Term Var)[x := n] = tabs V (e1[x := n]) := by rfl

lemma Term.subst_tm_tapp : (tapp e1 V : Term Var)[x := n] = tapp (e1 [x := n]) V := by rfl

lemma Term.subst_tm_let' : 
    (let' e1 e2 : Term Var)[x := n] = let' (e1 [x := n]) (e2[x := n]) := by rfl

lemma Term.subst_tm_inl : (inl e1 : Term Var)[x := n] = inl (e1[x := n]) := by rfl

lemma Term.subst_tm_inr : (inr e1 : Term Var)[x := n] = inr (e1[x := n]) := by rfl

lemma Term.subst_tm_case : 
    (case e1 e2 e3 : Term Var)[x := n] = case (e1[x := n]) (e2[x := n]) (e3[x := n]) := by rfl

@[scoped grind _=_]
lemma Term.subst_tm_def : Term.subst_tm (x : Var) (n : Term Var) (m : Term Var) = m[x := n] := 
  by rfl

end

/-- Binding substitution of types. -/
@[scoped grind =]
def Binding.subst (Z : Var) (P : Ty Var) : Binding Var → Binding Var
| sub T => sub (T[Z := P])
| ty  T => ty  (T[Z := P])

instance : HasSubstitution (Binding Var) Var (Ty Var) where
  subst m x n := Binding.subst x n m

omit [HasFresh Var]

lemma Binding.subst_sub {T n : Ty Var} {x : Var} : (sub T)[x := n] = sub (T[x := n]) := by rfl

lemma Binding.subst_ty {T n : Ty Var} {x : Var} : (ty T)[x := n] = ty (T[x := n]) := by rfl

end LambdaCalculus.LocallyNameless.Fsub
