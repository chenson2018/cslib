/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

import Cslib.Init
import Mathlib.Logic.Relation
import Mathlib.Data.List.TFAE

-- TODO: some of this should be upstreamed to Mathlib?
-- I'm going to put this all in `Relation` at the moment and worry about namepsacing cleanup later
namespace Relation

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen

-- TODO: grind pattern these with constraints
/-
#check ReflTransGen.single
#check ReflTransGen.trans
-/

variable {α : Type*} (r : α → α → Prop)

theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b := by
  induction h <;> grind

theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b := by
  induction h <;> grind

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen

-- TODO: more standard notation
local infix:50 " ⇓ " => Join (ReflTransGen r)
local infixr:50 " ⭢ " => r
local infixr:50 " ↠ " => ReflTransGen r
local infixr:50 " ≈ " => EqvGen r

/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Diamond := ∀ {A B C : α}, A ⭢ B → A ⭢ C → Join r B C

abbrev ChurchRosser := ∀ {x y}, x ≈ y → x ⇓ y

abbrev Confluent := Diamond (· ↠ ·)

abbrev Reducible (x : α) : Prop := ∃ y, r x y

abbrev Normal (x : α) : Prop := ¬Reducible r x

theorem normal_eq {r} (h : Normal r x) (xy : r x y) : x = y := by
  grind

@[grind =>]
theorem ReflTransGen.normal_eq {r} (h : Normal r x) (xy : ReflTransGen r x y) : x = y := by
  induction xy <;> grind 

abbrev SemiConfluent := ∀ {x y₁ y₂}, x ↠ y₂ → x ⭢ y₁ → y₁ ⇓ y₂

@[scoped grind →]
theorem confluent_toChurchRosser (h : Confluent r) : ChurchRosser r := by
  intro x y h_eqv
  induction h_eqv with
  | rel _ b => exists b; grind [ReflTransGen.single]
  | refl a => exists a
  | symm a b _ ih => exact symmetric_join ih
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨u, _, hbu⟩ := ih1
      obtain ⟨v, hbv, _⟩ := ih2
      obtain ⟨w, _, _⟩ := h hbu hbv
      exists w
      grind [ReflTransGen.trans]

@[scoped grind →]
theorem semiConfluent_toConfluent (h : SemiConfluent r) : Confluent r := by
  intro x y1 y2 h_xy1 h_xy2
  induction h_xy1 with
  | refl => use y2
  | tail h_xz h_zy1 ih =>
      obtain ⟨u, h_zu, _⟩ := ih
      obtain ⟨v, _, _⟩ := h h_zu h_zy1
      exists v
      grind [ReflTransGen.trans]

private theorem confluent_equivalents : [ChurchRosser r, SemiConfluent r, Confluent r].TFAE := by
  grind [List.tfae_cons_cons, List.tfae_singleton]

/-- Theorem 2.1.5 (3 ⇒ 1): Semi-confluence implies the Church-Rosser property. -/
theorem SemiConfluent_iff_ChurchRosser : SemiConfluent r ↔ ChurchRosser r :=
  List.TFAE.out (confluent_equivalents r) 1 0

theorem Confluent_iff_ChurchRosser : Confluent r ↔ ChurchRosser r :=
  List.TFAE.out (confluent_equivalents r) 2 0

theorem Confluent_iff_SemiConfluent : Confluent r ↔ SemiConfluent r :=
  List.TFAE.out (confluent_equivalents r) 2 1

theorem ChurchRosser_Normal₁ (cr : ChurchRosser r) (xy : x ≈ y) : Normal r y → x ↠ y := by
  have ⟨_, _, _⟩ := cr xy
  grind

theorem ChurchRosser_Normal₂ (cr : ChurchRosser r) (xy : x ≈ y)
    (ny : Normal r y) (nx : Normal r x) : x = y := by
  have ⟨_, _, _⟩ := cr xy
  grind

end Relation

/-! # Relations -/

namespace Cslib

universe u v

/-- The relation `r` 'up to' the relation `s`. -/
def Relation.UpTo (r s : α → α → Prop) : α → α → Prop := Relation.Comp s (Relation.Comp r s)

/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Diamond (R : α → α → Prop) := ∀ {A B C : α}, R A B → R A C → (∃ D, R B D ∧ R C D)

/-- A relation is confluent when its reflexive transitive closure has the diamond property. -/
abbrev Confluence (R : α → α → Prop) := Diamond (Relation.ReflTransGen R)

open _root_.Relation _root_.Relation.ReflTransGen in
/-- Extending a multistep reduction by a single step preserves multi-joinability. -/
lemma Relation.ReflTransGen.diamond_extend (h : Diamond R) :
  ReflTransGen R A B →
  R A C →
  ∃ D, Relation.ReflTransGen R B D ∧ Relation.ReflTransGen R C D := by
  intros AB _
  revert C
  induction AB using Relation.ReflTransGen.head_induction_on <;> intros C AC
  case refl => exact ⟨C, ⟨single AC, by rfl⟩⟩
  case head A'_C' _ ih =>
    obtain ⟨D, ⟨CD, C'_D⟩⟩ := h AC A'_C'
    obtain ⟨D', ⟨B_D', D_D'⟩⟩ := ih C'_D
    exact ⟨D', ⟨B_D', head CD D_D'⟩⟩

open _root_.Relation _root_.Relation.ReflTransGen in
/-- The diamond property implies confluence. -/
theorem Relation.ReflTransGen.diamond_confluence (h : Diamond R) : Confluence R := by
  intros A B C AB BC
  revert C
  induction AB using head_induction_on <;> intros C BC
  case refl => exists C
  case head _ _ A'_C' _ ih =>
    obtain ⟨D, ⟨CD, C'_D⟩⟩ := diamond_extend h BC A'_C'
    obtain ⟨D', ⟨B_D', D_D'⟩⟩ := ih C'_D
    exact ⟨D', ⟨B_D', ReflTransGen.trans CD D_D'⟩⟩

-- not sure why this doesn't compile as an "instance" but oh well
/-- A pair of subrelations lifts to transitivity on the relation. -/
def trans_of_subrelation {α : Type*} (s s' r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) (h' : ∀ a b : α, s' a b → r a b) : Trans s s' r where
  trans hab hbc := hr (h _ _ hab) (h' _ _ hbc)

/-- A subrelation lifts to transitivity on the left of the relation. -/
def trans_of_subrelation_left {α : Type*} (s r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) : Trans s r r where
  trans hab hbc := hr (h _ _ hab) hbc

/-- A subrelation lifts to transitivity on the right of the relation. -/
def trans_of_subrelation_right {α : Type*} (s r : α → α → Prop) (hr : Transitive r)
    (h : ∀ a b : α, s a b → r a b) : Trans r s r where
  trans hab hbc := hr hab (h _ _ hbc)

/-- This is a straightforward but useful specialisation of a more general result in
`Mathlib.Logic.Relation`. -/
theorem church_rosser_of_diamond {α : Type*} {r : α → α → Prop}
    (h : ∀ a b c, r a b → r a c → Relation.Join r b c) :
    Equivalence (Relation.Join (Relation.ReflTransGen r)) := by
  apply Relation.equivalence_join_reflTransGen
  intro a b c hab hac
  let ⟨d, hd⟩ := h a b c hab hac
  use d
  constructor
  · exact Relation.ReflGen.single hd.1
  · exact Relation.ReflTransGen.single hd.2

end Cslib
