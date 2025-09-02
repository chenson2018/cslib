/-
Copyright (c) 2025 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

import Cslib.Foundations.Syntax.HasWellFormed
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
@[simp, grind =]
def dom (Γ : Context Var Ty) : Finset Var := Γ.keys.toFinset

/-- A well-formed context. -/
abbrev Ok : Context Var Ty → Prop := NodupKeys

instance : HasWellFormed (Context Var Ty) :=
  ⟨Ok⟩

variable {Γ Δ : Context Var Ty}

omit [DecidableEq Var] in
@[grind _=_]
theorem haswellformed_def : Γ✓ = Γ.NodupKeys := by rfl

/-- Context membership implies membership in the domain. -/
@[scoped grind →]
theorem dom_mem (mem : ⟨x, σ⟩ ∈ Γ) : x ∈ Γ.dom := by
  simp only [dom, mem_toFinset, keys]
  grind

/-- Context membership is preserved on permuting a context. -/
theorem dom_perm_mem_iff (h : Γ.Perm Δ) {x : Var} : x ∈ Γ.dom ↔ x ∈ Δ.dom := by
  induction h <;> simp_all only [dom, mem_toFinset, keys_cons, mem_cons] 
  grind

omit [DecidableEq Var] in
/-- Context well-formedness is preserved on permuting a context. -/
@[scoped grind →]
theorem wf_perm (h : Γ.Perm Δ) : Γ✓ → Δ✓ := (List.perm_nodupKeys h).mp

omit [DecidableEq Var] in
/-- Context well-formedness is preserved on removing an element. -/
@[scoped grind →]
theorem wf_strengthen (ok : (Δ ++ ⟨x, σ⟩ :: Γ)✓) : (Δ ++ Γ)✓ := by
  exact List.NodupKeys.sublist (by simp) ok

@[simp, scoped grind]
def map_val (f : Ty → Ty) (Γ : Context Var Ty) : Context Var Ty := 
  Γ.map (fun ⟨var,ty⟩ => ⟨var,f ty⟩)

theorem map_val_ok (ok : Γ✓) (f : Ty → Ty) : (Γ.map_val f)✓ := by
  induction Γ
  case nil => grind
  case cons hd tl ih =>
    cases ok
    constructor <;> grind

lemma map_val_mem (mem : σ ∈ Γ.dlookup x) (f) : f σ ∈ (Γ.map_val f).dlookup x := by
  induction Γ
  case nil => simp at mem
  case cons hd tl ih =>
    let ⟨x',σ'⟩ := hd
    by_cases h : x = x'
    · subst h
      simp_all [map_val]
    · grind [List.dlookup_cons_ne]

end LambdaCalculus.LocallyNameless.Context

namespace List

variable {α : Type u} {β : α → Type v} 

variable [DecidableEq α]

-- TODO: this should upstream to Mathlib
@[grind]
theorem sublist_dlookup (l₁ l₂ : List (Sigma β)) (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
    (s : l₁ <+ l₂) (mem : b ∈ l₁.dlookup a) : b ∈ l₂.dlookup a := by
  induction s generalizing a b
  case slnil => exact mem
  case cons p' _ ih =>
    obtain ⟨a', b'⟩ := p'
    have : a ≠ a' := by
      have := ih nd₁ ?_ mem |> of_mem_dlookup |> mem_keys_of_mem
      all_goals grind [nodupKeys_cons]
    simp_all
  case cons₂ p' _ ih =>
    obtain ⟨a', b'⟩ := p'
    by_cases h : a = a'
    · subst h
      rw [List.dlookup_cons_eq] at *
      exact mem
    · simp_all

theorem dlookup_append_mem (l₁ l₂ : List (Sigma β)) (mem : b ∈ (l₁ ++ l₂).dlookup a) : 
    b ∈ l₁.dlookup a ∨ b ∈ l₂.dlookup a := by
  rw [List.dlookup_append l₁ l₂ a] at mem
  simp at mem
  grind

end List
