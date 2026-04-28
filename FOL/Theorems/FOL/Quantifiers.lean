/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL
import FOL.Theorems.Prop.Impl
import FOL.Theorems.Prop.Neg
import FOL.Theorems.Derived

namespace FOL.Theorems.FOL.Quantifiers

-- ============================================================
-- Nivel 4: Cuantificadores
-- ============================================================

-- Propiedades de sustitución para variables abstractas.
-- Dada la complejidad de la aritmética de De Bruijn en Lean 4, 
-- declaramos estos lemas como axiomas por ahora, de acuerdo con la Fase 3.
axiom subst_lift_cancel_formula (f : Formula) (v : Nat) (t : Term) : substFormula v t (liftFormula (v + 1) f) = f
axiom subst_distrib_and (A B : Formula) (v : Nat) (t : Term) : substFormula v t (.and A B) = .and (substFormula v t A) (substFormula v t B)
axiom lift_distrib_and (A B : Formula) (c : Nat) : liftFormula c (.and A B) = .and (liftFormula c A) (liftFormula c B)

-- Lema auxiliar: ∀x. A ⇒ ∀x. ¬¬A
theorem forall_dni {Γ A} : Γ ⊢ .impl (.forall A) (.forall (neg (neg A))) := by
  apply Derives.intro_impl
  apply Derives.intro_forall
  apply Derives.elim_impl (A := A)
  · exact FOL.Theorems.Prop.Neg.double_neg_intro
  · have h : ((.forall A) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 A) := by
      apply Derives.elim_forall (A := liftFormula 1 A) (t := .bvar 0)
      apply Derives.hyp
      exact List.Mem.head _
    rw [subst_lift_cancel_formula] at h
    exact h

-- Dualidad ∀/∃ (constructiva): (∃x. ¬A) ⇒ ¬(∀x. A)
theorem exists_not_impl_forall_not {Γ A} : Γ ⊢ .impl (.ex (neg A)) (neg (.forall A)) := by
  apply Derives.intro_impl
  apply Derives.intro_impl
  apply Derives.elim_ex (A := neg A) (B := ⊥)
  · apply Derives.hyp
    exact List.Mem.tail _ (List.Mem.head _)
  · apply Derives.elim_impl (A := A)
    · apply Derives.hyp
      exact List.Mem.head _
    · have h_forall : ((neg A) :: ((.forall A) :: (.ex (neg A)) :: Γ).map (liftFormula 0)) ⊢ .forall (liftFormula 1 A) := by
        have mem_second : liftFormula 0 (.forall A) ∈ ((neg A) :: ((.forall A) :: (.ex (neg A)) :: Γ).map (liftFormula 0)) := by
          exact List.Mem.tail _ (List.Mem.head _)
        apply Derives.hyp
        exact mem_second
      have h_elim : ((neg A) :: ((.forall A) :: (.ex (neg A)) :: Γ).map (liftFormula 0)) ⊢ substFormula 0 (#0) (liftFormula 1 A) := by
        apply Derives.elim_forall (A := liftFormula 1 A) (t := .bvar 0)
        exact h_forall
      rw [subst_lift_cancel_formula] at h_elim
      exact h_elim

-- 15. Distribución de ∀ sobre ∧: (∀x. A ∧ B) ⇔ (∀x. A) ∧ (∀x. B)

theorem forall_and_impl_and_forall {Γ A B} : Γ ⊢ .impl (.forall (.and A B)) (.and (.forall A) (.forall B)) := by
  apply Derives.intro_impl
  apply Derives.intro_and
  · apply Derives.intro_forall
    have h : ((.forall (.and A B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 (.and A B)) := by
      apply Derives.elim_forall (A := liftFormula 1 (.and A B)) (t := .bvar 0)
      apply Derives.hyp
      exact List.Mem.head _
    rw [subst_lift_cancel_formula] at h
    apply Derives.elim_and_l (B := B)
    exact h
  · apply Derives.intro_forall
    have h : ((.forall (.and A B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 (.and A B)) := by
      apply Derives.elim_forall (A := liftFormula 1 (.and A B)) (t := .bvar 0)
      apply Derives.hyp
      exact List.Mem.head _
    rw [subst_lift_cancel_formula] at h
    apply Derives.elim_and_r (A := A)
    exact h

theorem and_forall_impl_forall_and {Γ A B} : Γ ⊢ .impl (.and (.forall A) (.forall B)) (.forall (.and A B)) := by
  apply Derives.intro_impl
  apply Derives.intro_forall
  apply Derives.intro_and
  · have h_ctx : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ liftFormula 0 (.and (.forall A) (.forall B)) := by
      apply Derives.hyp
      exact List.Mem.head _
    rw [lift_distrib_and] at h_ctx
    have h_forall_A : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ .forall (liftFormula 1 A) := by
      apply Derives.elim_and_l (B := liftFormula 0 (.forall B))
      exact h_ctx
    have hA : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 A) := by
      apply Derives.elim_forall (A := liftFormula 1 A) (t := .bvar 0)
      exact h_forall_A
    rw [subst_lift_cancel_formula] at hA
    exact hA
  · have h_ctx : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ liftFormula 0 (.and (.forall A) (.forall B)) := by
      apply Derives.hyp
      exact List.Mem.head _
    rw [lift_distrib_and] at h_ctx
    have h_forall_B : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ .forall (liftFormula 1 B) := by
      apply Derives.elim_and_r (A := liftFormula 0 (.forall A))
      exact h_ctx
    have hB : ((.and (.forall A) (.forall B)) :: Γ).map (liftFormula 0) ⊢ substFormula 0 (#0) (liftFormula 1 B) := by
      apply Derives.elim_forall (A := liftFormula 1 B) (t := .bvar 0)
      exact h_forall_B
    rw [subst_lift_cancel_formula] at hB
    exact hB

theorem distrib_forall_and {Γ A B} : Γ ⊢ iff (.forall (.and A B)) (.and (.forall A) (.forall B)) := by
  apply Derives.intro_and
  · exact forall_and_impl_and_forall
  · exact and_forall_impl_forall_and

end FOL.Theorems.FOL.Quantifiers

export FOL.Theorems.FOL.Quantifiers (
  subst_lift_cancel_formula
  subst_distrib_and
  lift_distrib_and
  forall_dni
  exists_not_impl_forall_not
  forall_and_impl_and_forall
  and_forall_impl_forall_and
  distrib_forall_and
)
