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
-- @axiom_system: classical
-- @importance: high

import FOL.FOL

namespace FOL.Theorems.Prop.Neg

-- ============================================================
-- Nivel 2: Propiedades de la Negación
-- ============================================================

-- 5. Explosión (Ex Falso Quodlibet): ⊥ ⇒ A
theorem explosion_impl {Γ A} : Γ ⊢ .impl ⊥ A := by
  apply Derives.intro_impl
  apply Derives.bot_elim
  apply Derives.hyp
  exact List.Mem.head _

-- Regla Clásica Derivada (Reductio ad Absurdum)
-- Si asumimos Eliminación de la Doble Negación (DNE) en el contexto
theorem derived_raa {Γ A} (h_dne : .impl (neg (neg A)) A ∈ Γ) (h : neg A :: Γ ⊢ ⊥) : Γ ⊢ A := by
  apply Derives.elim_impl (A := neg (neg A))
  · apply Derives.hyp
    exact h_dne
  · apply Derives.intro_impl
    exact h

-- 6. Doble Negación (Introducción): A ⇒ ¬(¬A)
theorem double_neg_intro {Γ A} : Γ ⊢ .impl A (neg (neg A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := A)
  · apply Derives.hyp
    exact List.Mem.head _
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)

-- 7. Doble Negación (Eliminación): ¬(¬A) ⇒ A
-- Requiere DNE en el contexto por definición (trivial en este caso, pero ilustrativo)
theorem double_neg_elim {Γ A} (h_dne : .impl (neg (neg A)) A ∈ Γ) : Γ ⊢ .impl (neg (neg A)) A := by
  apply Derives.hyp
  exact h_dne

-- 8. Contrapositiva (1): (A ⇒ B) ⇒ (¬B ⇒ ¬A)
theorem contrapositive_1 {Γ A B} : Γ ⊢ .impl (.impl A B) (.impl (neg B) (neg A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_impl (A := B)
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.hyp
      exact List.Mem.head _

-- 9. Contrapositiva (2): (¬B ⇒ ¬A) ⇒ (A ⇒ B)
-- Requiere DNE para B en el contexto
theorem contrapositive_2 {Γ A B} (h_dne : .impl (neg (neg B)) B ∈ Γ) : Γ ⊢ .impl (.impl (neg B) (neg A)) (.impl A B) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply derived_raa
  · exact List.Mem.tail _ (List.Mem.tail _ h_dne)
  · apply Derives.elim_impl (A := A)
    · apply Derives.elim_impl (A := neg B)
      · apply Derives.hyp
        exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · apply Derives.hyp
        exact List.Mem.head _
    · apply Derives.hyp
      exact List.Mem.tail _ (List.Mem.head _)

end FOL.Theorems.Prop.Neg

export FOL.Theorems.Prop.Neg (
  explosion_impl
  derived_raa
  double_neg_intro
  double_neg_elim
  contrapositive_1
  contrapositive_2
)
