/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Mathlib
import Cslib.Data.HasFresh
import Cslib.Syntax.HasSubstitution
import Cslib.Computability.LambdaCalculus.LocallyNameless.Untyped.AesopRuleset
import Cslib.Computability.LambdaCalculus.LocallyNameless.Context

/-! # λ-calculus

The polymorphic λ-calculus, with a locally nameless representation of syntax.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* See also <https://www.cis.upenn.edu/~plclub/popl08-tutorial/code/>, from which
  this is partially adapted

-/

universe u v

variable {V : Type u} {B : Type v} [DecidableEq V]

namespace LambdaCalculus.LocallyNameless.Polymorphic

/-- Types of the polymorphic lambda calculus. -/
inductive Ty (V : Type u) (B : Type v)
  /-- A base type, from a typing context. -/
  | base : B → Ty V B
  /-- A function type. -/
  | arrow : Ty V B → Ty V B → Ty V B
  /-- Bound type variables that appear under a univeral quantification, using a de-Bruijn index. -/
  | bvar : ℕ → Ty V B
  /-- Free type variables. -/
  | fvar : V → Ty V B
  /-- A universal quantification. -/
  | all : Ty V B → Ty V B → Ty V B

scoped infixr:70 " ⤳ " => Ty.arrow

/-- Syntax of locally nameless terms, with free variables over `V` and base types over `B`. -/
inductive Term (V : Type u) (B : Type v)
  /-- Bound term variables that appear under a lambda abstraction, using a de-Bruijn index. -/
  | bvar : ℕ → Term V B
  /-- Free term variables. -/
  | fvar : V → Term V B
  /-- Lambda abstraction, introducing a new bound term variable. -/
  | abs  : Ty V B → Term V B → Term V B
  /-- Function application. -/
  | app  : Term V B → Term V B → Term V B
  /-- Type abstraction, introducing a new bound type variable. -/
  | tabs  : Ty V B → Term V B → Term V B
  /-- Type application. -/
  | tapp  : Term V B → Ty V B → Term V B

/-- Opening of a type, replacing the ith bound type variable with a type. -/
def Ty.openRec (i : ℕ) (sub : Ty V B) : Ty V B → Ty V B
| base b => base b
| bvar i'   => if i = i' then sub else bvar i'
| fvar x    => fvar x
| arrow l r => arrow (openRec i sub l) (openRec i sub r)
| all l r   => all (openRec i sub l) (openRec (i + 1) sub r)

def Term.openRec_ty (i : ℕ) (sub : Ty V B) : Term V B → Term V B
| bvar i    => bvar i
| fvar x    => fvar x
| app l r   => app (openRec_ty i sub l) (openRec_ty i sub r)
| abs ty t  => abs  (Ty.openRec i sub ty) (openRec_ty i sub t)
| tabs ty t => tabs (Ty.openRec i sub ty) (openRec_ty i sub t)
| tapp t ty => tapp (openRec_ty i sub t) (Ty.openRec i sub ty)

def Term.openRec_tm (i : ℕ) (sub : Term V B) : Term V B → Term V B
| bvar i'  => if i == i' then sub else bvar i'
| fvar x   => fvar x
| abs ty t => abs ty (Term.openRec_tm (i + 1) sub t)
| app l r  => app (Term.openRec_tm i sub l) (Term.openRec_tm i sub r)
| tabs ty t => tabs ty (Term.openRec_tm i sub t)
| tapp t ty => tapp (Term.openRec_tm i sub t) ty

scoped notation:68 e "⟦" i " ↝ " sub "⟧"=> Ty.openRec i sub e
scoped notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.openRec_ty i sub e
scoped notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.openRec_tm i sub e


def Ty.open' (T U : Ty V B) := Ty.openRec 0 U T
def Term.open_ty (e : Term V B) U := Term.openRec_ty 0 U e
def Term.open_tm (e1 : Term V B) e2 := Term.openRec_tm 0 e2 e1

infixr:80 " ^ " => Ty.open'
infixr:80 " ^ " => Term.open_ty
infixr:80 " ^ " => Term.open_tm

inductive Ty.LC : Ty V B → Prop
| fvar : LC (fvar x)
| arrow : LC l → LC r → LC (arrow l r)
| all (L : Finset V) : LC T1 → (∀ X ∉ L, LC (T2 ^ fvar X)) → LC (all T1 T2)

inductive Term.LC : Term V B → Prop
| fvar : LC (fvar x)
| abs {T : Ty V B} (L : Finset V) : T.LC → (∀ x ∉  L, LC (e1 ^ fvar x)) → LC (abs T e1)
| app : LC l → LC r → LC (app l r)
| tabs {T : Ty V B} (L : Finset V) : T.LC → (∀ X ∉ L, LC (e1 ^ fvar X)) → LC (abs T e1)
| tapp : e1.LC → T.LC → LC (tapp e1 T)

def Term.body (e : Term V B) := ∃ L : Finset V, ∀ x ∉ L, LC (e ^ fvar x)

end LambdaCalculus.LocallyNameless.Polymorphic
