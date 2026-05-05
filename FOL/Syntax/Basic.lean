/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- This is the foundational module. All other modules import it.

import Init.Classical
open Classical
universe u

/-! ### ExistsUnique — Unique Existence ###

  Custom implementation of ∃! independent of Lean's standard library.
  Provides a complete API via dot-notation and Peano-compatible aliases.

  Definition: p has a unique witness iff ∃ x, p x ∧ ∀ y, p y → y = x
-/

def ExistsUnique {α : Sort u} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ ∀ y, p y → y = x

/-! ### Notation ###
  ∃! x, p   — standard-looking notation (overrides Lean built-in ∃!)
  ∃¹ x, p   — safe notation (no clash risk, Peano-style, 4 variants) -/

syntax "∃! " ident ", " term : term
macro_rules
  | `(∃! $x, $p) => `(ExistsUnique fun $x => $p)

syntax "∃¹ " ident ", " term : term
syntax "∃¹ " "(" ident ")" ", " term : term
syntax "∃¹ " "(" ident " : " term ")" ", " term : term
syntax "∃¹ " ident " : " term ", " term : term
macro_rules
  | `(∃¹ $x:ident, $p:term)                     => `(ExistsUnique (fun $x => $p))
  | `(∃¹ ($x:ident), $p:term)                   => `(ExistsUnique (fun $x => $p))
  | `(∃¹ ($x:ident : $t:term), $p:term)         => `(ExistsUnique (fun ($x : $t) => $p))
  | `(∃¹ $x:ident : $t:term, $p:term)           => `(ExistsUnique (fun ($x : $t) => $p))

/-! ### API — dot-notation style ### -/

/-- Constructor: witness + property + uniqueness proof → ExistsUnique -/
theorem ExistsUnique.intro {α : Sort u} {p : α → Prop} (w : α)
    (hw : p w) (h : ∀ y, p y → y = w) : ExistsUnique p :=
  ⟨w, hw, h⟩

/-- Extract ∃ x, p x from ExistsUnique p -/
theorem ExistsUnique.exists {α : Sort u} {p : α → Prop} (h : ExistsUnique p) :
    ∃ x, p x := by
  obtain ⟨x, hx, _⟩ := h
  exact ⟨x, hx⟩

/-- Extract the unique witness (noncomputable) -/
noncomputable def ExistsUnique.choose {α : Sort u} {p : α → Prop} (h : ExistsUnique p) : α :=
  Classical.choose (ExistsUnique.exists h)

/-- The witness satisfies the property -/
theorem ExistsUnique.choose_spec {α : Sort u} {p : α → Prop} (h : ExistsUnique p) :
    p (h.choose) := by
  obtain ⟨x, hx, _⟩ := h
  exact Classical.choose_spec ⟨x, hx⟩

/-- Uniqueness: any y satisfying p equals the witness -/
theorem ExistsUnique.unique {α : Sort u} {p : α → Prop} (h : ExistsUnique p) :
    ∀ y, p y → y = h.choose := by
  intro y hy
  unfold choose
  have h_exists := ExistsUnique.exists h
  have h_spec   := Classical.choose_spec h_exists
  obtain ⟨x, _, hunique⟩ := h
  have h_choose_eq_x : Classical.choose h_exists = x := hunique _ h_spec
  rw [h_choose_eq_x]
  exact hunique y hy

/-! ### API — Peano-compatible aliases ###

  Mirror the Peano.PeanoNatLib naming convention for cross-project compatibility.
  These are thin wrappers; no new logic. -/

/-- Alias for ExistsUnique.choose (Peano style) -/
noncomputable def choose_unique {α : Sort u} {p : α → Prop} (h : ExistsUnique p) : α :=
  h.choose

/-- Alias for ExistsUnique.choose_spec (Peano style) -/
theorem choose_spec_unique {α : Sort u} {p : α → Prop} (h : ExistsUnique p) :
    p (choose_unique h) :=
  h.choose_spec

/-- Alias for ExistsUnique.unique with implicit y (Peano argument style) -/
theorem choose_uniq {α : Sort u} {p : α → Prop} (h : ExistsUnique p) {y : α} (hy : p y) :
    y = choose_unique h :=
  h.unique y hy

/-! ### User definitions go below this line ###
  Add preliminary definitions, notations, and helper lemmas specific
  to your project here. -/
