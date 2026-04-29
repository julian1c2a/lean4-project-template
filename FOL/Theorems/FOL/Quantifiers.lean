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

-- Los dos lemas de distribución son directamente reducciones definitionales.
theorem subst_distrib_and (A B : Formula) (v : Nat) (t : Term) :
    substFormula v t (.and A B) = .and (substFormula v t A) (substFormula v t B) := rfl

theorem lift_distrib_and (A B : Formula) (c : Nat) :
    liftFormula c (.and A B) = .and (liftFormula c A) (liftFormula c B) := rfl

-- Lemas de cancelación en términos (para la prueba de subst_lift_cancel_formula).
-- La identidad substTerm v (bvar v) (liftTerm (v+1) t) = t se verifica
-- por inducción estructural sobre Term/List Term.
mutual
theorem substTerm_liftTerm_cancel (v : Nat) (t : Term) :
    substTerm v (.bvar v) (liftTerm (v + 1) t) = t := by
  match t with
  | .bvar n =>
    simp only [liftTerm]
    -- Goal: substTerm v (#v) (if n < v + 1 then #n else #(n + 1)) = #n
    split
    · -- h1 : n < v + 1  →  liftTerm gives #n
      next h1 =>
      simp only [substTerm]
      -- Goal: (if n = v then #v else if v < n then #(n-1) else #n) = #n
      split
      · -- h2 : n = v
        next h2 => exact congrArg Term.bvar h2.symm
      · -- h2 : n ≠ v
        next h2 =>
        split
        · -- h3 : v < n, contradicts h1 : n < v+1
          next h3 => omega
        · -- ¬(v < n) and n ≠ v: n < v → result is #n
          rfl
    · -- h1 : ¬(n < v + 1)  →  liftTerm gives #(n+1)
      next h1 =>
      simp only [substTerm]
      -- Goal: (if n+1 = v then #v else if v < n+1 then #(n+1-1) else #(n+1)) = #n
      split
      · -- h2 : n+1 = v, contradicts h1
        next h2 => omega
      · -- h2 : n+1 ≠ v
        next h2 =>
        split
        · -- h3 : v < n+1 → result is #(n+1-1) = #n  (definitionally)
          rfl
        · -- h3 : ¬(v < n+1), contradicts h1
          next h3 => omega
  | .fvar _ => rfl
  | .func f ts =>
    simp only [liftTerm, substTerm]
    exact congrArg (Term.func f) (substTerms_liftTerms_cancel v ts)

theorem substTerms_liftTerms_cancel (v : Nat) (ts : List Term) :
    substTerms v (.bvar v) (liftTerms (v + 1) ts) = ts := by
  match ts with
  | []        => rfl
  | t :: ts'  =>
    simp only [liftTerms, substTerms]
    rw [substTerm_liftTerm_cancel v t, substTerms_liftTerms_cancel v ts']
end

-- substFormula v (bvar v) (liftFormula (v+1) f) = f
-- Propiedad clave de De Bruijn: sustituir la variable libre v por (bvar v)
-- tras un lift en (v+1) recupera la fórmula original.
theorem subst_lift_cancel_formula (f : Formula) (v : Nat) :
    substFormula v (.bvar v) (liftFormula (v + 1) f) = f := by
  induction f generalizing v with
  | bottom => rfl
  | eq t1 t2 =>
    show Formula.eq (substTerm v (.bvar v) (liftTerm (v + 1) t1))
                    (substTerm v (.bvar v) (liftTerm (v + 1) t2)) = Formula.eq t1 t2
    rw [substTerm_liftTerm_cancel v t1, substTerm_liftTerm_cancel v t2]
  | atom p ts =>
    show Formula.atom p (substTerms v (.bvar v) (liftTerms (v + 1) ts)) = Formula.atom p ts
    rw [substTerms_liftTerms_cancel v ts]
  | impl f1 f2 ih1 ih2 =>
    show Formula.impl (substFormula v (.bvar v) (liftFormula (v + 1) f1))
                      (substFormula v (.bvar v) (liftFormula (v + 1) f2)) = Formula.impl f1 f2
    rw [ih1 v, ih2 v]
  | and f1 f2 ih1 ih2 =>
    show Formula.and (substFormula v (.bvar v) (liftFormula (v + 1) f1))
                     (substFormula v (.bvar v) (liftFormula (v + 1) f2)) = Formula.and f1 f2
    rw [ih1 v, ih2 v]
  | or f1 f2 ih1 ih2 =>
    show Formula.or (substFormula v (.bvar v) (liftFormula (v + 1) f1))
                    (substFormula v (.bvar v) (liftFormula (v + 1) f2)) = Formula.or f1 f2
    rw [ih1 v, ih2 v]
  | «forall» f1 ih =>
    -- liftFormula (v+1) (∀.f1) = ∀.(liftFormula (v+2) f1)
    -- substFormula v (bvar v) (∀.X) = ∀.(substFormula (v+1) (liftTerm 0 (bvar v)) X)
    -- liftTerm 0 (bvar v) = bvar (v+1)  (since v : Nat ≥ 0, so v < 0 is false)
    show Formula.forall (substFormula (v + 1) (liftTerm 0 (.bvar v)) (liftFormula (v + 2) f1)) =
         Formula.forall f1
    have hlift : liftTerm 0 (Term.bvar v) = Term.bvar (v + 1) := by
      simp only [liftTerm]
      split
      · next h => omega   -- v < 0, impossible for Nat
      · rfl
    rw [hlift]; exact congrArg Formula.forall (ih (v + 1))
  | ex f1 ih =>
    show Formula.ex (substFormula (v + 1) (liftTerm 0 (.bvar v)) (liftFormula (v + 2) f1)) =
         Formula.ex f1
    have hlift : liftTerm 0 (Term.bvar v) = Term.bvar (v + 1) := by
      simp only [liftTerm]
      split
      · next h => omega
      · rfl
    rw [hlift]; exact congrArg Formula.ex (ih (v + 1))

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
