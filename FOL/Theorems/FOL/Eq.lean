/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Tactics
-- @axiom_system: none
-- @importance: high

import FOL.FOL
import FOL.Tactics.Basic

namespace FOL.Theorems.FOL.Eq

-- ============================================================
-- Teoremas Derivados de la Igualdad
-- ============================================================

-- Lemas de sintaxis auxiliar (protección de términos al sustituir)
mutual
def subst_lift_term_cancel (t : Term) (s : Term) (v : Nat) :
    substTerm v s (liftTerm v t) = t := by
  match t with
  | .bvar n =>
    dsimp [liftTerm]
    split
    · rename_i h
      unfold substTerm
      have h1 : ¬(n = v) := by omega
      have h2 : ¬(n > v) := by omega
      simp [h1, h2]
    · rename_i h
      unfold substTerm
      have h1 : ¬(n + 1 = v) := by omega
      have h2 : n + 1 > v := by omega
      have h3 : n + 1 - 1 = n := by omega
      simp [h1, h2, h3]
  | .fvar x => rfl
  | .func f ts =>
    dsimp [liftTerm, substTerm]
    congr 1
    exact subst_lift_terms_cancel ts s v

def subst_lift_terms_cancel (ts : List Term) (s : Term) (v : Nat) :
    substTerms v s (liftTerms v ts) = ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    dsimp [liftTerms, substTerms]
    congr 1
    · exact subst_lift_term_cancel t s v
    · exact subst_lift_terms_cancel ts' s v
end

theorem substTerms_append (v : Nat) (s : Term) (ts1 ts2 : List Term) :
    substTerms v s (ts1 ++ ts2) = substTerms v s ts1 ++ substTerms v s ts2 := by
  induction ts1 with
  | nil => rfl
  | cons t ts ih => simp only [substTerms, ih, List.cons_append]

-- Simetría de la igualdad: t1 = t2 ⊢ t2 = t1
theorem eq_symm {Γ : List Formula} {t1 t2 : Term} (h : Γ ⊢ .eq t1 t2) : Γ ⊢ .eq t2 t1 := by
  let A := Formula.eq (.bvar 0) (liftTerm 0 t1)
  have hSubst1 : substFormula 0 t1 A = .eq t1 t1 := by
    dsimp [A, substFormula, substTerm]
    rw [subst_lift_term_cancel]
  have hSubst2 : substFormula 0 t2 A = .eq t2 t1 := by
    dsimp [A, substFormula, substTerm]
    rw [subst_lift_term_cancel]
  have hRefl := Derives.eq_refl Γ t1
  rw [← hSubst1] at hRefl
  have hSubst := Derives.eq_subst Γ A t1 t2 h hRefl
  rw [hSubst2] at hSubst
  exact hSubst

-- Transitividad de la igualdad: t1 = t2, t2 = t3 ⊢ t1 = t3
theorem eq_trans {Γ : List Formula} {t1 t2 t3 : Term}
    (h12 : Γ ⊢ .eq t1 t2) (h23 : Γ ⊢ .eq t2 t3) : Γ ⊢ .eq t1 t3 := by
  let A := Formula.eq (liftTerm 0 t1) (.bvar 0)
  have hSubst2 : substFormula 0 t2 A = .eq t1 t2 := by
    dsimp [A, substFormula, substTerm]
    rw [subst_lift_term_cancel]
  have hSubst3 : substFormula 0 t3 A = .eq t1 t3 := by
    dsimp [A, substFormula, substTerm]
    rw [subst_lift_term_cancel]
  rw [← hSubst2] at h12
  have hSubst := Derives.eq_subst Γ A t2 t3 h23 h12
  rw [hSubst3] at hSubst
  exact hSubst

-- Congruencia de funciones: t1 = t2 ⊢ f(..., t1, ...) = f(..., t2, ...)
theorem eq_func {Γ : List Formula} {f : String} {pre post : List Term} {t1 t2 : Term}
    (hEq : Γ ⊢ .eq t1 t2) : Γ ⊢ .eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t2 :: post)) := by
  let A := Formula.eq (.func f (liftTerms 0 pre ++ liftTerm 0 t1 :: liftTerms 0 post))
                      (.func f (liftTerms 0 pre ++ .bvar 0 :: liftTerms 0 post))
  have hSubst1 : substFormula 0 t1 A = .eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t1 :: post)) := by
    dsimp [A, substFormula, substTerm]
    rw [substTerms_append, substTerms_append]
    simp [substTerms, substTerm, subst_lift_terms_cancel, subst_lift_term_cancel]
  have hSubst2 : substFormula 0 t2 A = .eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t2 :: post)) := by
    dsimp [A, substFormula, substTerm]
    rw [substTerms_append, substTerms_append]
    simp [substTerms, substTerm, subst_lift_terms_cancel, subst_lift_term_cancel]
  have hRefl := Derives.eq_refl Γ (.func f (pre ++ t1 :: post))
  rw [← hSubst1] at hRefl
  have hDer := Derives.eq_subst Γ A t1 t2 hEq hRefl
  rw [hSubst2] at hDer
  exact hDer

-- Congruencia de predicados (átomos): t1 = t2, P(..., t1, ...) ⊢ P(..., t2, ...)
theorem eq_atom {Γ : List Formula} {p : String} {pre post : List Term} {t1 t2 : Term}
    (hEq : Γ ⊢ .eq t1 t2) (hAtom : Γ ⊢ .atom p (pre ++ t1 :: post)) : Γ ⊢ .atom p (pre ++ t2 :: post) := by
  let A := Formula.atom p (liftTerms 0 pre ++ .bvar 0 :: liftTerms 0 post)
  have hSubst1 : substFormula 0 t1 A = .atom p (pre ++ t1 :: post) := by
    dsimp [A, substFormula, substTerm]
    rw [substTerms_append]
    simp [substTerms, substTerm, subst_lift_terms_cancel]
  have hSubst2 : substFormula 0 t2 A = .atom p (pre ++ t2 :: post) := by
    dsimp [A, substFormula, substTerm]
    rw [substTerms_append]
    simp [substTerms, substTerm, subst_lift_terms_cancel]
  rw [← hSubst1] at hAtom
  have hDer := Derives.eq_subst Γ A t1 t2 hEq hAtom
  rw [hSubst2] at hDer
  exact hDer

end FOL.Theorems.FOL.Eq

export FOL.Theorems.FOL.Eq (eq_symm eq_trans eq_func eq_atom)
