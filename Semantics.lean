/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL
-- @axiom_system: classical
-- @importance: high

import FOL.FOL

namespace FOL.Metamath.Semantics

-- ============================================================
-- Fase 5: Semántica y Modelos
-- ============================================================

structure Model (D : Type) where
  func : String → List D → D
  rel  : String → List D → Prop

mutual
def evalTerm {D : Type} (M : Model D) (v : Nat → D) (t : Term) : D :=
  match t with
  | .var n => v n
  | .func f ts => M.func f (evalTerms M v ts)

def evalTerms {D : Type} (M : Model D) (v : Nat → D) (ts : List Term) : List D :=
  match ts with
  | [] => []
  | t :: ts' => evalTerm M v t :: evalTerms M v ts'
end

def shiftEnv {D : Type} (v : Nat → D) (d : D) : Nat → D
  | 0 => d
  | n + 1 => v n

def updateEnv {D : Type} (c : Nat) (v : Nat → D) (d : D) : Nat → D :=
  fun n =>
    if n < c then v n
    else if n = c then d
    else v (n - 1)

@[simp]
theorem updateEnv_zero {D : Type} (v : Nat → D) (d : D) (n : Nat) :
    updateEnv 0 v d n = shiftEnv v d n := by
  cases n <;> simp [updateEnv, shiftEnv]

def evalFormula {D : Type} (M : Model D) (v : Nat → D) (f : Formula) : Prop :=
  match f with
  | .bottom => False
  | .eq t1 t2 => evalTerm M v t1 = evalTerm M v t2
  | .atom p ts => M.rel p (evalTerms M v ts)
  | .impl f1 f2 => evalFormula M v f1 → evalFormula M v f2
  | .forall f1 => ∀ (d : D), evalFormula M (shiftEnv v d) f1
  | .and f1 f2 => evalFormula M v f1 ∧ evalFormula M v f2
  | .or f1 f2 => evalFormula M v f1 ∨ evalFormula M v f2
  | .ex f1 => ∃ (d : D), evalFormula M (shiftEnv v d) f1

def contextSatisfies {D : Type} (M : Model D) (v : Nat → D) (Γ : List Formula) : Prop :=
  ∀ f, f ∈ Γ → evalFormula M v f

def satisfies (Γ : List Formula) (f : Formula) : Prop :=
  ∀ (D : Type) (M : Model D) (v : Nat → D), contextSatisfies M v Γ → evalFormula M v f

-- ============================================================
-- Lemas de Sustitución Semántica (Lifting y Sustitución)
-- ============================================================

-- 1. Lemas generalizados para Términos (Profundidad 'c')

mutual
theorem eval_liftTerm_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (t : Term) :
    evalTerm M (updateEnv c v d) (liftTerm c t) = evalTerm M v t := by
  match t with
  | .var n =>
    unfold liftTerm evalTerm updateEnv
    split
    · rename_i h
      simp [h]
    · rename_i h
      have h1 : ¬(n + 1 < c) := by omega
      have h2 : ¬(n + 1 = c) := by omega
      have h3 : n + 1 - 1 = n := by omega
      simp [h, h1, h2, h3]
  | .func f ts =>
    unfold liftTerm evalTerm
    have ih := eval_liftTerms_ext M v d c ts
    rw [ih]

theorem eval_liftTerms_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (ts : List Term) :
    evalTerms M (updateEnv c v d) (liftTerms c ts) = evalTerms M v ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold liftTerms evalTerms
    have ih1 := eval_liftTerm_ext M v d c t
    have ih2 := eval_liftTerms_ext M v d c ts'
    rw [ih1, ih2]
end

mutual
theorem eval_substTerm_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (t : Term) :
    evalTerm M v (substTerm c s t) = evalTerm M (updateEnv c v (evalTerm M v s)) t := by
  match t with
  | .var n =>
    unfold substTerm evalTerm updateEnv
    split
    · rename_i h
      have h1 : ¬(n < c) := by omega
      simp [h, h1]
    · rename_i h
      split
      · rename_i h2
        have h3 : ¬(n < c) := by omega
        have h4 : ¬(n = c) := by omega
        simp [h3, h4]
      · rename_i h2
        have h3 : n < c := by omega
        simp [h3]
  | .func f ts =>
    unfold substTerm evalTerm
    have ih := eval_substTerms_ext M v s c ts
    rw [ih]

theorem eval_substTerms_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (ts : List Term) :
    evalTerms M v (substTerms c s ts) = evalTerms M (updateEnv c v (evalTerm M v s)) ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold substTerms evalTerms
    have ih1 := eval_substTerm_ext M v s c t
    have ih2 := eval_substTerms_ext M v s c ts'
    rw [ih1, ih2]
end

-- 2. Lemas generalizados para Fórmulas (Firmas)

theorem eval_liftFormula_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (f : Formula) :
    evalFormula M (updateEnv c v d) (liftFormula c f) ↔ evalFormula M v f := by
  sorry

theorem eval_substFormula_ext {D : Type} (M : Model D) (v : Nat → D) (t : Term) (c : Nat) (f : Formula) :
    evalFormula M v (substFormula c t f) ↔ evalFormula M (updateEnv c v (evalTerm M v t)) f := by
  sorry

@[simp]
theorem eval_liftFormula_zero {D : Type} (M : Model D) (v : Nat → D) (d : D) (f : Formula) :
    evalFormula M (shiftEnv v d) (liftFormula 0 f) ↔ evalFormula M v f := by
  sorry

@[simp]
theorem eval_substFormula_zero {D : Type} (M : Model D) (v : Nat → D) (t : Term) (f : Formula) :
    evalFormula M v (substFormula 0 t f) ↔ evalFormula M (shiftEnv v (evalTerm M v t)) f := by
  sorry

theorem contextSatisfies_lift_zero {D : Type} (M : Model D) (v : Nat → D) (d : D) {Γ : List Formula} :
    contextSatisfies M (shiftEnv v d) (Γ.map (liftFormula 0)) ↔ contextSatisfies M v Γ := by
  sorry

-- ============================================================
-- Lemas de Corrección de Reescritura Local
-- ============================================================

theorem rule_soundness {D : Type} (M : Model D) (v : Nat → D) {A B : Formula} (h : LocalRule A B) :
    evalFormula M v A ↔ evalFormula M v B := by
  sorry

theorem replaceAt_soundness {D : Type} (M : Model D) (v : Nat → D) {f sub sub' : Formula} {p : Pos}
    (hGet : getAt? f p = some sub) (hEq : evalFormula M v sub ↔ evalFormula M v sub') :
    evalFormula M v f ↔ evalFormula M v (replaceAt f p sub') := by
  sorry

end FOL.Metamath.Semantics
