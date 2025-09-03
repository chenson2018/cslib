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

variable {α : Type u} [DecidableEq α]

-- TODO: These are pieces of API that cannot be directly automated by adding `grind` attributes to
-- `Mathlib.Data.List.Sigma`. We should consider upstreaming them to Mathlib.
namespace List

variable {β : α → Type v} {Γ Δ : List (Sigma β)}

/-- List permutation preserves keys. -/
theorem perm_keys (h : Γ.Perm Δ) : x ∈ Γ.keys ↔ x ∈ Δ.keys := by
  induction h <;> grind [keys_cons]

/-- Sublists without duplicate keys preserve lookups. -/
@[grind]
theorem sublist_dlookup (l₁ l₂ : List (Sigma β)) (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
    (s : l₁ <+ l₂) (mem : b ∈ l₁.dlookup a) : b ∈ l₂.dlookup a := by
  induction s generalizing a b
  case slnil => exact mem
  case cons p' _ ih =>
    obtain ⟨a', b'⟩ := p'
    have := ih nd₁ (by grind [nodupKeys_cons]) mem |> of_mem_dlookup |> mem_keys_of_mem
    have : a ≠ a' := by grind [nodupKeys_cons]
    simp_all
  case cons₂ p' _ ih =>
    obtain ⟨a', b'⟩ := p'
    by_cases h : a = a'
    · subst h
      rw [List.dlookup_cons_eq] at *
      exact mem
    · simp_all

/-- A lookup in appended lists must appear in one of the lists. -/
theorem dlookup_append_mem (l₁ l₂ : List (Sigma β)) (mem : b ∈ (l₁ ++ l₂).dlookup a) : 
    b ∈ l₁.dlookup a ∨ b ∈ l₂.dlookup a := by
  rw [List.dlookup_append l₁ l₂ a] at mem
  simp at mem
  grind

end List

namespace LambdaCalculus.LocallyNameless

variable {β : Type v}

/-- A typing context is a list of free variables and corresponding types. -/
abbrev Context (α : Type u) (β : Type v) := List ((_ : α) × β)

namespace Context

-- we would like grind to see through certain notations
attribute [scoped grind] Option.mem_def
attribute [scoped grind _=_] List.append_eq
attribute [scoped grind] List.Nodup
attribute [scoped grind] List.NodupKeys

-- we would like grind to treat list and finset membership the same
attribute [scoped grind] List.mem_toFinset

-- otherwise, we mostly reuse existing API in `Mathlib.Data.List.Sigma`
attribute [scoped grind] List.keys
attribute [scoped grind →] List.mem_keys_of_mem
attribute [scoped grind] List.dlookup_isSome
attribute [scoped grind] List.perm_nodupKeys
attribute [scoped grind →] List.perm_nodupKeys
attribute [scoped grind →] List.Perm.symm

/-- The domain of a context is the finite set of free variables it uses. -/
@[simp, scoped grind =]
def dom (Γ : Context α β) : Finset α := Γ.keys.toFinset

/-- A well-formed context has no duplicate keys. -/
instance : HasWellFormed (Context α β) :=
  ⟨List.NodupKeys⟩

omit [DecidableEq α] in
@[scoped grind _=_]
theorem haswellformed_def (Γ : Context α β) : Γ✓ = Γ.NodupKeys := by rfl

variable {Γ Δ : Context α β}

/-- A mapping of values within a context. -/
@[simp, scoped grind]
def map_val (f : β → β) (Γ : Context α β) : Context α β := 
  Γ.map (fun ⟨var,ty⟩ => ⟨var,f ty⟩)

/-- A mapping of values preserves non-duplication of keys. -/
theorem map_val_ok (ok : Γ✓) (f : β → β) : (Γ.map_val f)✓ := by
  induction Γ
  case nil => grind
  case cons hd tl ih =>
    cases ok
    constructor <;> grind

/-- A mapping of values preserves lookups. -/
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
