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
import FOL.Tactics

namespace FOL.Theorems.Eq

-- ============================================================
-- Teoremas Derivados de la Igualdad
-- ============================================================

-- Lemas de sintaxis auxiliar (protección de términos al sustituir)
mutual
lemma subst_lift_term_cancel (t : Term) (s : Term) (v : Nat) :
    substTerm v s (liftTerm v t) = t := by
  match t with
  | .var n =>
    dsimp [liftTerm, substTerm]
    split
    · rename_i h; simp [h]
    · rename_i h
      have h1 : ¬(n + 1 = v) := by omega
      have h2 : n + 1 > v := by omega
      have h3 : n + 1 - 1 = n := by omega
      simp [h1, h2, h3]
  | .func f ts =>
    dsimp [liftTerm, substTerm]
    congr 1
    exact subst_lift_terms_cancel ts s v

lemma subst_lift_terms_cancel (ts : List Term) (s : Term) (v : Nat) :
    substTerms v s (liftTerms v ts) = ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    dsimp [liftTerms, substTerms]
    congr 1
    · exact subst_lift_term_cancel t s v
    · exact subst_lift_terms_cancel ts' s v
end

-- Simetría de la igualdad: t1 = t2 ⊢ t2 = t1
theorem eq_symm {Γ : List Formula} {t1 t2 : Term} (h : Γ ⊢ .eq t1 t2) : Γ ⊢ .eq t2 t1 := by
  let A := Formula.eq (.var 0) (liftTerm 0 t1)
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
  let A := Formula.eq (liftTerm 0 t1) (.var 0)
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

end FOL.Theorems.Eq

export FOL.Theorems.Eq (eq_symm eq_trans)
