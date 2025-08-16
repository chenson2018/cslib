/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Data.HasFresh
import Cslib.Syntax.HasSubstitution
import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.AesopRuleset
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

inductive Ty (Var : Type u)
  | top : Ty Var
  | bvar : ℕ → Ty Var
  | fvar : Var → Ty Var
  | arrow : Ty Var → Ty Var → Ty Var
  | all : Ty Var → Ty Var → Ty Var
  | sum : Ty Var → Ty Var → Ty Var

inductive Term (Var : Type u)
  | bvar : ℕ → Term Var
  | fvar : Var → Term Var
  | abs : Ty Var → Term Var → Term Var
  | app : Term Var → Term Var → Term Var
  | tabs : Ty Var → Term Var → Term Var
  | tapp : Term Var → Ty Var → Term Var
  | let' : Term Var → Term Var → Term Var
  | inl : Term Var → Term Var
  | inr : Term Var → Term Var
  | case : Term Var → Term Var → Term Var → Term Var

def Ty.open_tt_rec (K : ℕ) (U T : Ty Var) : Ty Var :=
  match T with
  | top => top
  | bvar J => if K == J then U else (bvar J)
  | fvar X => fvar X
  | arrow T1 T2 => arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | all T1 T2 => all (open_tt_rec K U T1) (open_tt_rec (K + 1) U T2)
  | sum T1 T2 => sum (open_tt_rec K U T1) (open_tt_rec K U T2)

def Term.open_te_rec (K : ℕ) (U : Ty Var) (e : Term Var) : Term Var :=
  match e with
  | bvar i => bvar i
  | fvar x => fvar x
  | abs V e1 => abs (Ty.open_tt_rec K U V) (open_te_rec K U e1)
  | app e1 e2 => app (open_te_rec K U e1) (open_te_rec K U e2)
  | tabs V e1 => tabs (Ty.open_tt_rec K U V) (open_te_rec (K + 1) U e1)
  | tapp e1 V => tapp (open_te_rec K U e1) (Ty.open_tt_rec K U V)
  | let' e1 e2 => let' (open_te_rec K U e1) (open_te_rec K U e2)
  | inl e1 => inl (open_te_rec K U e1)
  | inr e2 => inr (open_te_rec K U e2)
  | case e1 e2 e3 =>
      case (open_te_rec K U e1) (open_te_rec K U e2) (open_te_rec K U e3)

def Term.open_ee_rec (k : ℕ) (f : Term Var) (e : Term Var) : Term Var :=
  match e with
  | bvar i => if k == i then f else (bvar i)
  | fvar x => fvar x
  | abs V e1 => abs V (open_ee_rec (k + 1) f e1)
  | app e1 e2 => app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | tabs V e1 => tabs V (open_ee_rec k f e1)
  | tapp e1 V => tapp (open_ee_rec k f e1) V
  | let' e1 e2 => let' (open_ee_rec k f e1) (open_ee_rec (k + 1) f e2)
  | inl e1 => inl (open_ee_rec k f e1)
  | inr e2 => inr (open_ee_rec k f e2)
  | case e1 e2 e3 =>
      case (open_ee_rec k f e1)
               (open_ee_rec (k + 1) f e2)
               (open_ee_rec (k + 1) f e3)

def open_tt (T U : Ty Var) := Ty.open_tt_rec 0 U T
def open_te (e : Term Var) U := Term.open_te_rec 0 U e
def open_ee (e1 e2 : Term Var) := Term.open_ee_rec 0 e2 e1

inductive Ty.LC : Ty Var → Prop
  | top : LC top
  | var : LC (fvar X)
  | arrow : LC T1 → LC T2 → LC (arrow T1 T2)
  | all (L : Finset Var) : LC T1 → (∀ X ∉ L, LC (open_tt T2 (fvar X))) → LC (all T1 T2)
  | sum :LC T1 → LC T2 → LC (sum T1 T2)

inductive Term.LC : Term Var → Prop
  | var : LC (fvar x)
  | abs (L : Finset Var) : T.LC → (∀ x ∉ L, LC (open_ee e1 (fvar x))) → LC (abs T e1)
  | app : LC e1 → LC e2 → LC (app e1 e2)
  | tabs (L : Finset Var) : T.LC → (∀ X ∉ L, LC (open_te e1 (Ty.fvar X))) → LC (tabs T e1)
  | tapp : LC e1 → V.LC → LC (tapp e1 V)
  | let' (L : Finset Var) : LC e1 → (∀ x ∉ L, LC (open_ee e2 (fvar x))) → LC (let' e1 e2)
  | inl : LC e1 → LC (inl e1)
  | inr : LC e1 → LC (inr e1)
  | case (L : Finset Var) :
      LC e1 →
      (∀ x ∉ L, LC (open_ee e2 (fvar x))) →
      (∀ x ∉ L, LC (open_ee e3 (fvar x))) →
      LC (case e1 e2 e3)

def Term.body (e : Term Var) := ∃ L : Finset Var, ∀ x ∉ L, LC (open_ee e (fvar x))

inductive Binding (Var : Type u) : Type (u + 1)
  | sub : Ty Var → Binding Var
  | ty : Ty Var → Binding Var

abbrev Env (Var : Type u) := List ((_ : Var) × Binding Var)

inductive Ty.wf : Env Var → Ty Var → Prop
  | top : wf E top
  | var : E.dlookup X = some (Binding.sub U) → wf E (fvar X)
  | arrow : wf E T1 → wf E T2 → wf E (arrow T1 T2)
  | all (L : Finset Var) : 
      wf E T1 →
      (∀ X ∉ L, wf ([⟨X,Binding.sub T1⟩] ++ E) (open_tt T2 (fvar X))) →
      wf E (all T1 T2)
  | sum : wf E T1 → wf E T2 → wf E (sum T1 T2)

inductive Env.wf : Env Var → Prop
  | empty : wf []
  | sub : wf E → T.wf E → X ∉ Context.dom E → wf ([⟨X, Binding.sub T⟩] ++ E)
  | ty : wf E → T.wf E → x ∉ Context.dom E → wf ([⟨x, Binding.ty T⟩] ++ E)

inductive Ty.Sub : Env Var → Ty Var → Ty Var → Prop
  | top : E.wf → S.wf E → Sub E S top
  | refl_tvar : E.wf → (fvar X).wf E → Sub E (fvar X) (fvar X)
  | trans_tvar : E.dlookup X = some (Binding.sub U) → Sub E U T → Sub E (fvar X) T
  | arrow : Sub E T1 S1 → Sub E S2 T2 → Sub E (arrow S1 S2) (arrow T1 T2)
  | all (L : Finset Var) :
      Sub E T1 S1 →
      (∀ X ∉ L, Sub ([⟨X, Binding.sub T1⟩] ++ E) (open_tt S2 (fvar X)) (open_tt T2 (fvar X))) →
      Sub E (all S1 S2) (all T1 T2)
  | sum : Sub E S1 T1 → Sub E S2 T2 → Sub E (sum S1 S2) (sum T1 T2)

open Term Ty in
inductive Typing : Env Var → Term Var → Ty Var → Prop
  | var : E.wf → E.dlookup x = some (Binding.ty T) → Typing E (fvar x) T
  | abs (L : Finset Var) :
      (∀ x ∉ L, Typing ([⟨x, Binding.ty V⟩] ++ E) (open_ee e1 (fvar x)) T1) →
      Typing E (abs V e1) (arrow V T1)
  | app : Typing E e1 (arrow T1 T2) → Typing E e2 T1 → Typing E (app e1 e2) T2
  | tabs (L : Finset Var) :
      (∀ X ∉ L, Typing ([⟨X, Binding.sub V⟩] ++ E) (open_te e1 (fvar X)) (open_tt T1 (fvar X))) →
      Typing E (tabs V e1) (all V T1)
  | tapp : Typing E e1 (all T1 T2) → Sub E T T1 → Typing E (tapp e1 T) (open_tt T2 T)
  | sub : Typing E e S → Sub E S T → Typing E e T
  | let' (L : Finset Var) :
      Typing E e1 T1 →
      (∀ x ∉ L, Typing ([⟨x, Binding.ty T1⟩] ++ E) (open_ee e2 (fvar x)) T2) →
      Typing E (let' e1 e2) T2
  | inl : Typing E e1 T1 → T2.wf E → Typing E (inl e1) (sum T1 T2)
  | inr : Typing E e1 T2 → T1.wf E → Typing E (inr e1) (sum T1 T2)
  | case (L : Finset Var) :
      Typing E e1 (sum T1 T2) →
      (∀ x ∉ L, Typing ([⟨x, Binding.ty T1⟩] ++ E) (open_ee e2 (fvar x)) T) →
      (∀ x ∉ L, Typing ([⟨x, Binding.ty T2⟩] ++ E) (open_ee e3 (fvar x)) T) →
      Typing E (case e1 e2 e3) T

inductive Term.Value : Term Var → Prop
  | abs : LC (abs T e1) → Value (abs T e1)
  | tabs : LC (tabs T e1) → Value (tabs T e1)
  | inl : Value e1 → Value (inl e1)
  | inr : Value e1 → Value (inr e1)

inductive Term.Red : Term Var → Term Var → Prop
  | app_1 : LC e2 → Red e1 e1' → Red (app e1 e2) (app e1' e2)
  | app_2 : Value e1 → Red e2 e2' → Red (app e1 e2) (app e1 e2')
  | tapp : V.LC → Red e1 e1' → Red (tapp e1 V) (tapp e1' V)
  | abs : LC (abs T e1) → Value v2 → Red (app (abs T e1) v2) (open_ee e1 v2)
  | tabs : LC (tabs T1 e1) → T2.LC → Red (tapp (tabs T1 e1) T2) (open_te e1 T2)
  | let_1 : Red e1 e1' → e2.body → Red (let' e1 e2) (let' e1' e2)
  | let' : Value v1 → e2.body → Red (let' v1 e2) (open_ee e2 v1)
  | inl_1 : Red e1 e1' → Red (inl e1) (inl e1')
  | inr_1 : Red e1 e1' → Red (inr e1) (inr e1')
  | case_1 : Red e1 e1' → e2.body → e3.body → Red (case e1 e2 e3) (case e1' e2 e3)
  | case_inl : Value v1 → e2.body → e3.body → Red (case (inl v1) e2 e3) (open_ee e2 v1)
  | case_inr : Value v1 → e2.body → e3.body → Red (case (inr v1) e2 e3) (open_ee e3 v1)

end LambdaCalculus.LocallyNameless.Fsub
