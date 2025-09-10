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

/-- Computes the difference of `l₁` and `l₂`, by removing each matching key in `l₂` from `l₁`. -/
def kdiff : List (Sigma β) → List (Sigma β) → List (Sigma β)
  | l, [] => l
  | l₁, ⟨a,_⟩ :: l₂ => if a ∈ l₁.keys then (l₁.kerase a).kdiff l₂ else l₁.kdiff l₂

@[simp] theorem kdiff_nil (l : List (Sigma β)) : l.kdiff [] = l := by rfl

@[simp] theorem kdiff_cons (l₁ l₂ : List (Sigma β)) (s : Sigma β) : 
    l₁.kdiff (s :: l₂) = (l₁.kerase s.fst).kdiff l₂ := by
  simp_all [List.kdiff]

theorem kdiff_cons_right (l₁ l₂ : List (Sigma β)) (s : (Sigma β)) : 
    l₁.kdiff (s :: l₂) = (l₁.kdiff l₂).kerase s.fst := by
  symm; induction l₂ generalizing l₁ <;> simp_all [kerase_comm]

theorem kdiff_kerase (l₁ l₂ : List (Sigma β)) (s : Sigma β) : 
    (l₁.kdiff l₂).kerase s.fst = (l₁.kerase s.fst).kdiff l₂ := by
  rw [← kdiff_cons_right, kdiff_cons]

@[simp] theorem nil_kdiff (l : List (Sigma β)) : [].kdiff l = [] := by
  induction l <;> simp_all

theorem cons_kdiff (s : Sigma β) (l₁ l₂ : List (Sigma β)) :
    (s :: l₁).kdiff l₂ = 
    if s.fst ∈ l₂.keys then l₁.kdiff (l₂.kerase s.fst) else s :: l₁.kdiff l₂ := by
  induction l₂ generalizing l₁ with
  | nil => rfl
  | cons s' l₂ ih =>
    by_cases h : s.fst = s'.fst
    next => simp [*]
    next =>
      have := Ne.symm h
      simp_all

variable {s : Sigma β} {l₁ l₂ : List (Sigma β)}

theorem cons_kdiff_of_mem (h : s.fst ∈ l₂.keys) (l₁ : List (Sigma β)) :
    (s :: l₁).kdiff l₂ = l₁.kdiff (l₂.kerase s.fst) := by rw [cons_kdiff, if_pos h]

theorem cons_kdiff_of_not_mem (h : s.fst ∉ l₂.keys) (l₁ : List (Sigma β)) :
    (s :: l₁).kdiff l₂ = s :: l₁.kdiff l₂ := by rw [cons_kdiff, if_neg h]

theorem kdiff_eq_foldl : ∀ l₁ l₂ : List (Sigma β),
    l₁.kdiff l₂ = foldl (fun l ⟨a,_⟩ => l.kerase a) l₁ l₂
  | _, [] => rfl
  | l₁, a :: l₂ => (kdiff_cons l₁ l₂ a).trans (kdiff_eq_foldl _ _)

@[simp] theorem kdiff_append (l₁ l₂ l₃ : List (Sigma β)) : 
    l₁.kdiff (l₂ ++ l₃) = (l₁.kdiff l₂).kdiff l₃ := by
  simp only [kdiff_eq_foldl, foldl_append]

theorem kdiff_sublist : ∀ l₁ l₂ : List (Sigma β), (l₁.kdiff l₂).Sublist l₁
  | _, [] => .refl _
  | l₁, ⟨a,b⟩ :: l₂ => by
    calc
      l₁.kdiff (⟨a,b⟩ :: l₂) = (l₁.kerase a).kdiff l₂ := kdiff_cons ..
      _ <+ l₁.kerase a := kdiff_sublist ..
      _ <+ l₁ := kerase_sublist ..

theorem kdiff_subset (l₁ l₂ : List (Sigma β)) : l₁.kdiff l₂ ⊆ l₁ := (kdiff_sublist ..).subset

/-
theorem mem_diff_of_mem {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁ → a ∉ l₂ → a ∈ l₁.diff l₂
  | _, [], h₁, _ => h₁
  | l₁, b :: l₂, h₁, h₂ => by
    rw [diff_cons]
    exact mem_diff_of_mem ((mem_erase_of_ne <| ne_of_not_mem_cons h₂).2 h₁) (mt (.tail _) h₂)

theorem Sublist.diff_right : ∀ {l₁ l₂ l₃ : List α}, l₁ <+ l₂ → l₁.diff l₃ <+ l₂.diff l₃
  | _,  _, [], h => h
  | l₁, l₂, a :: l₃, h => by simp only [diff_cons, (h.erase _).diff_right]

theorem Sublist.erase_diff_erase_sublist {a : α} :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
  | [], _, _ => erase_sublist
  | b :: l₁, l₂, h => by
    if heq : b = a then
      simp [heq]
    else
      simp [heq, erase_comm a]
      exact (erase_cons_head b _ ▸ h.erase b).erase_diff_erase_sublist
-/

/-- List permutation preserves keys. -/
@[grind =>]
theorem perm_keys (h : Γ.Perm Δ) : x ∈ Γ.keys ↔ x ∈ Δ.keys := by
  induction h <;> grind [keys_cons]

omit [DecidableEq α] in
theorem mem_keys_append_NodupKeys (mem : X ∈ Γ.keys) (ok : (Δ ++ Γ).NodupKeys) : X ∉ Δ.keys := by
  induction Δ <;> simp_all [keys] ; grind

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

theorem nmem_append_keys (l₁ l₂ : List (Sigma β)) :
    a ∉ (l₁ ++ l₂).keys ↔ a ∉ l₁.keys ∧ a ∉ l₂.keys := by
  constructor <;> (
    intro h
    induction l₂
    case nil => simp_all
    case cons hd tl ih =>
      have perm : (l₁ ++ hd :: tl).Perm (hd :: (l₁ ++ tl)) := by simp
      grind [keys_cons]
  )

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

-- a few grinds on Option:
attribute [scoped grind =] Option.or_eq_some_iff
attribute [scoped grind =] Option.or_eq_none_iff

-- we would like grind to treat list and finset membership the same
attribute [scoped grind] List.mem_toFinset

-- otherwise, we mostly reuse existing API in `Mathlib.Data.List.Sigma`
attribute [scoped grind] List.keys
attribute [scoped grind] List.keys_cons
attribute [scoped grind →] List.mem_keys_of_mem
attribute [scoped grind] List.dlookup_isSome
attribute [scoped grind →] List.perm_nodupKeys
attribute [scoped grind →] List.Perm.symm
attribute [scoped grind _=_] List.dlookup_append
attribute [scoped grind =] List.dlookup_cons_eq
attribute [scoped grind =] List.dlookup_cons_ne
attribute [scoped grind =] List.dlookup_nil

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

omit [DecidableEq α] in
/-- A mapping of values preserves keys. -/
@[scoped grind]
lemma map_val_keys (f) : Γ.keys = (Γ.map_val f).keys := by
  induction Γ  <;> simp_all

omit [DecidableEq α] in
/-- A mapping of values preserves non-duplication of keys. -/
theorem map_val_ok (ok : Γ✓) (f : β → β) : (Γ.map_val f)✓ := by
  grind

/-- A mapping of values maps lookups. -/
lemma map_val_mem (mem : σ ∈ Γ.dlookup x) (f) : f σ ∈ (Γ.map_val f).dlookup x := by
  induction Γ <;> grind

/-- A mapping of values preserves non-lookups. -/
lemma map_val_nmem (nmem : Γ.dlookup x = none) (f) : (Γ.map_val f).dlookup x = none := by
  grind [List.dlookup_eq_none]

end LambdaCalculus.LocallyNameless.Context
