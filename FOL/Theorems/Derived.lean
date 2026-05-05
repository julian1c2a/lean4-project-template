/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Prelim
-- @axiom_system: constructive
-- @importance: high

import FOL.FOL
import FOL.Theorems.Prop.Neg

namespace FOL.Theorems.Derived

-- ============================================================
-- Nivel 3: Conectivos Primitivos (y sus propiedades)
-- ============================================================

-- Introducción de la conjunción: A ⇒ B ⇒ A ∧ B
theorem and_intro {Γ A B} : Γ ⊢ .impl A (.impl B (.and A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_and
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.hyp; exact List.Mem.head _

-- Eliminación de la conjunción (1): (A ∧ B) ⇒ A
theorem and_elim_left {Γ A B} : Γ ⊢ .impl (.and A B) A := by
  apply Derives.intro_impl
  apply Derives.elim_and_l (B := B)
  apply Derives.hyp
  exact List.Mem.head _

-- Eliminación de la conjunción (2): (A ∧ B) ⇒ B
theorem and_elim_right {Γ A B} : Γ ⊢ .impl (.and A B) B := by
  apply Derives.intro_impl
  apply Derives.elim_and_r (A := A)
  apply Derives.hyp
  exact List.Mem.head _

-- Introducción de la disyunción (1): A ⇒ A ∨ B
theorem or_intro_left {Γ A B} : Γ ⊢ .impl A (.or A B) := by
  apply Derives.intro_impl
  apply Derives.intro_or_l (B := B)
  apply Derives.hyp
  exact List.Mem.head _

-- Introducción de la disyunción (2): B ⇒ A ∨ B
theorem or_intro_right {Γ A B} : Γ ⊢ .impl B (.or A B) := by
  apply Derives.intro_impl
  apply Derives.intro_or_r (A := A)
  apply Derives.hyp
  exact List.Mem.head _

-- Eliminación de la disyunción: (A ∨ B) ⇒ (A ⇒ C) ⇒ (B ⇒ C) ⇒ C
theorem or_elim {Γ A B C} : Γ ⊢ .impl (.or A B) (.impl (.impl A C) (.impl (.impl B C) C)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_or (A := A) (B := B)
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.elim_impl (A := B)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
    · apply Derives.hyp; exact List.Mem.head _

-- Conmutatividad de la conjunción: (A ∧ B) ⇒ (B ∧ A)
theorem and_comm {Γ A B} : Γ ⊢ .impl (.and A B) (.and B A) := by
  apply Derives.intro_impl
  apply Derives.intro_and
  · apply Derives.elim_and_r (A := A)
    apply Derives.hyp; exact List.Mem.head _
  · apply Derives.elim_and_l (B := B)
    apply Derives.hyp; exact List.Mem.head _

-- Conmutatividad de la disyunción: (A ∨ B) ⇒ (B ∨ A)
theorem or_comm {Γ A B} : Γ ⊢ .impl (.or A B) (.or B A) := by
  apply Derives.intro_impl
  apply Derives.elim_or (A := A) (B := B)
  · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.intro_or_r (A := B)
    apply Derives.hyp; exact List.Mem.head _
  · apply Derives.intro_or_l (B := A)
    apply Derives.hyp; exact List.Mem.head _

-- Asociatividad de la conjunción: ((A ∧ B) ∧ C) ⇒ (A ∧ (B ∧ C))
theorem and_assoc {Γ A B C} : Γ ⊢ .impl (.and (.and A B) C) (.and A (.and B C)) := by
  apply Derives.intro_impl
  apply Derives.intro_and
  · apply Derives.elim_and_l (B := B)
    apply Derives.elim_and_l (B := C)
    apply Derives.hyp; exact List.Mem.head _
  · apply Derives.intro_and
    · apply Derives.elim_and_r (A := A)
      apply Derives.elim_and_l (B := C)
      apply Derives.hyp; exact List.Mem.head _
    · apply Derives.elim_and_r (A := .and A B)
      apply Derives.hyp; exact List.Mem.head _

-- Asociatividad de la disyunción: ((A ∨ B) ∨ C) ⇒ (A ∨ (B ∨ C))
theorem or_assoc {Γ A B C} : Γ ⊢ .impl (.or (.or A B) C) (.or A (.or B C)) := by
  apply Derives.intro_impl
  apply Derives.elim_or (A := .or A B) (B := C)
  · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.elim_or (A := A) (B := B)
    · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.intro_or_l (B := .or B C)
      apply Derives.hyp; exact List.Mem.head _
    · apply Derives.intro_or_r (A := A)
      apply Derives.intro_or_l (B := C)
      apply Derives.hyp; exact List.Mem.head _
  · apply Derives.intro_or_r (A := A)
    apply Derives.intro_or_r (A := B)
    apply Derives.hyp; exact List.Mem.head _

-- Ley de De Morgan (1): ¬(A ∨ B) ⇒ ¬A ∧ ¬B
theorem de_morgan_1_fwd {Γ A B} : Γ ⊢ .impl (neg (.or A B)) (.and (neg A) (neg B)) := by
  apply Derives.intro_impl
  apply Derives.intro_and
  · apply Derives.intro_impl
    apply Derives.elim_impl (A := .or A B)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
    · apply Derives.intro_or_l (B := B)
      apply Derives.hyp; exact List.Mem.head _
  · apply Derives.intro_impl
    apply Derives.elim_impl (A := .or A B)
    · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
    · apply Derives.intro_or_r (A := A)
      apply Derives.hyp; exact List.Mem.head _

-- Ley de De Morgan (1) reverso: ¬A ∧ ¬B ⇒ ¬(A ∨ B)
theorem de_morgan_1_rev {Γ A B} : Γ ⊢ .impl (.and (neg A) (neg B)) (neg (.or A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_or (A := A) (B := B)
  · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.elim_impl (A := A)
    · apply Derives.elim_and_l (B := neg B)
      apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp; exact List.Mem.head _
  · apply Derives.elim_impl (A := B)
    · apply Derives.elim_and_r (A := neg A)
      apply Derives.hyp; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp; exact List.Mem.head _

-- Ley de De Morgan (1) completa: ¬(A ∨ B) ⇔ ¬A ∧ ¬B
theorem de_morgan_1 {Γ A B} : Γ ⊢ iff (neg (.or A B)) (.and (neg A) (neg B)) := by
  apply Derives.intro_and
  · exact de_morgan_1_fwd
  · exact de_morgan_1_rev

-- Ley de De Morgan (2) reverso (Constructivo): ¬A ∨ ¬B ⇒ ¬(A ∧ B)
theorem de_morgan_2_rev {Γ A B} : Γ ⊢ .impl (.or (neg A) (neg B)) (neg (.and A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_or (A := neg A) (B := neg B)
  · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.elim_and_l (B := B)
      apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := B)
    · apply Derives.hyp; exact List.Mem.head _
    · apply Derives.elim_and_r (A := A)
      apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)

end FOL.Theorems.Derived

export FOL.Theorems.Derived (
  and_intro
  and_elim_left
  and_elim_right
  or_intro_left
  or_intro_right
  or_elim
  and_comm
  or_comm
  and_assoc
  or_assoc
  de_morgan_1_fwd
  de_morgan_1_rev
  de_morgan_1
  de_morgan_2_rev
)
