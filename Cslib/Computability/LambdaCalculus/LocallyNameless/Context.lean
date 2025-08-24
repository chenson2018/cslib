/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Syntax.HasWellFormed
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Sigma

/-! # λ-calculus

Contexts as pairs of free variables and types.

-/

universe u v

variable {Var : Type u} {Ty : Type v} [DecidableEq Var]

namespace LambdaCalculus.LocallyNameless

/-- A typing context is a list of free variables and corresponding types. -/
abbrev Context (Var : Type u) (Ty : Type v) := List ((_ : Var) × Ty)

namespace Context

open List

/-- The domain of a context is the finite set of free variables it uses. -/
@[simp, scoped grind =]
def dom : Context Var Ty → Finset Var := toFinset ∘ keys

/-- A well-formed context. -/
abbrev Ok : Context Var Ty → Prop := NodupKeys

instance : HasWellFormed (Context Var Ty) :=
  ⟨Ok⟩

variable {Γ Δ : Context Var Ty}

/-- Context membership is preserved on permuting a context. -/
theorem dom_perm_mem_iff (h : Γ.Perm Δ) {x : Var} : x ∈ Γ.dom ↔ x ∈ Δ.dom := by
  induction h <;> simp_all only [dom, Function.comp_apply, mem_toFinset, keys_cons, mem_cons] 
  grind

/-- Context membership implies membership in the domain. -/
@[scoped grind →]
theorem dom_mem (mem : ⟨x, σ⟩ ∈ Γ) : x ∈ Γ.dom := by
  simp only [dom, Function.comp_apply, mem_toFinset, keys]
  grind

-- TODO: shouldn't need to restate this, but some downstream grind doesn't work without it
-- TODO: instead of =, use ∈ notation on option? (may be why grind wasn't working)
@[scoped grind →]
theorem of_mem_dlookup (mem : Γ.dlookup x = some T) : ⟨x, T⟩ ∈ Γ := by
  exact List.of_mem_dlookup mem

omit [DecidableEq Var] in
/-- Context well-formedness is preserved on permuting a context. -/
@[scoped grind →]
theorem wf_perm (h : Γ.Perm Δ) : Γ✓ → Δ✓ := (List.perm_nodupKeys h).mp

omit [DecidableEq Var] in
/-- Context well-formedness is preserved on removing an element. -/
@[scoped grind →]
theorem wf_strengthen (ok : (Δ ++ ⟨x, σ⟩ :: Γ)✓) : (Δ ++ Γ)✓ := by
  exact List.NodupKeys.sublist (by simp) ok

end LambdaCalculus.LocallyNameless.Context
