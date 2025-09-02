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

variable {Γ Δ Θ : Env Var} {σ : Ty Var}

namespace Ty.Sub

open scoped Ty.Wf Env.Wf

omit [HasFresh Var] in
lemma refl (wf_Γ : Γ.Wf) (wf_σ : σ.Wf Γ) : Sub Γ σ σ := by
  induction wf_σ with
  | all => apply all (free_union [Context.dom] Var) <;> grind
  | _ => grind

lemma weaken (sub : Sub (Γ ++ Θ) σ σ') (wf : (Γ ++ Δ ++ Θ).Wf) : Sub (Γ ++ Δ ++ Θ) σ σ' := by
  generalize eq : Γ ++ Θ = ΓΘ at sub
  induction sub generalizing Γ 
  case trans_tvar => sorry
  case all => sorry
  all_goals grind  

end Ty.Sub

end LambdaCalculus.LocallyNameless.Fsub
