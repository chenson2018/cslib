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

omit [HasFresh Var] [DecidableEq Var] in
 /-- An opening appearing in both sides of an equality of terms can be removed. -/
@[grind]
lemma Ty.open_lc_aux (T : Ty Var) j V i U (neq : i ≠ j) (h : T⟦j ↝ V⟧ = (T⟦j ↝ V⟧)⟦i ↝ U⟧) : 
    T = T⟦i ↝ U⟧ := by induction T generalizing j i <;> grind

lemma Ty.open_lc (T : Ty Var) U k (lc : T.LC) : T = T⟦k ↝ U⟧ := by
  induction lc generalizing k
  case all => 
    -- TODO: how to tell grind to try `free_union`?
    let ⟨x, _⟩ := fresh_exists <| free_union (free := fv) Var
    grind
  all_goals grind

end LambdaCalculus.LocallyNameless.Fsub
