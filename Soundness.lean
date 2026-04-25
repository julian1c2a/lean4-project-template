/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Metamath.Semantics, FOL.Tactics
-- @axiom_system: classical
-- @importance: high

import FOL.FOL
import FOL.Tactics
import FOL.Metamath.Semantics

namespace FOL.Metamath.Soundness

local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- Fase 5: Teorema de Corrección (Soundness)
-- ============================================================

theorem soundness {Γ f} (h : Γ ⊢ f) : Γ ⊨ f := by
  induction h with
  | hyp _ f' hIn =>
    intro D M v hΓ
    exact hΓ f' hIn
  | intro_impl _ _ _ _ ih =>
    intro D M v hΓ hA
    apply ih D M v
    intro f' hf'
    cases hf' with
    | head _ => exact hA
    | tail _ hTail => exact hΓ f' hTail
  | elim_impl _ _ _ _ _ ih_impl ih_A =>
    intro D M v hΓ
    exact (ih_impl D M v hΓ) (ih_A D M v hΓ)
  | intro_and _ _ _ _ _ ihA ihB =>
    intro D M v hΓ
    exact ⟨ihA D M v hΓ, ihB D M v hΓ⟩
  | elim_and_l _ _ _ _ ih =>
    intro D M v hΓ
    exact (ih D M v hΓ).left
  | elim_and_r _ _ _ _ ih =>
    intro D M v hΓ
    exact (ih D M v hΓ).right
  | intro_or_l _ _ _ _ ih =>
    intro D M v hΓ
    exact Or.inl (ih D M v hΓ)
  | intro_or_r _ _ _ _ ih =>
    intro D M v hΓ
    exact Or.inr (ih D M v hΓ)
  | elim_or _ _ _ _ _ _ _ ih_or ih_A ih_B =>
    intro D M v hΓ
    cases ih_or D M v hΓ with
    | inl hA =>
      apply ih_A D M v
      intro f' hf'
      cases hf' with
      | head _ => exact hA
      | tail _ hTail => exact hΓ f' hTail
    | inr hB =>
      apply ih_B D M v
      intro f' hf'
      cases hf' with
      | head _ => exact hB
      | tail _ hTail => exact hΓ f' hTail
  | bot_elim _ _ _ ih =>
    intro D M v hΓ
    have hBot := ih D M v hΓ
    contradiction
  | eq_refl _ _ =>
    intro D M v _
    simp only [evalFormula]
  | eq_subst _ A t1 t2 _ _ ih_eq ih_A =>
    intro D M v hΓ
    have hEq := ih_eq D M v hΓ
    have hA := ih_A D M v hΓ
    simp only [evalFormula] at hEq
    have hSubst1 := (eval_substFormula_zero M v t1 A).mp hA
    rw [hEq] at hSubst1
    exact (eval_substFormula_zero M v t2 A).mpr hSubst1
  | weakening _ _ _ _ hSubset ih =>
    intro D M v hΓ
    apply ih D M v
    intro g hg
    exact hΓ g (hSubset g hg)
  | intro_forall Γ' _ _ ih =>
    intro D M v hΓ d
    have hCtx : contextSatisfies M (shiftEnv v d) (Γ'.map (liftFormula 0)) :=
      (contextSatisfies_lift_zero M v d).mpr hΓ
    exact ih D M (shiftEnv v d) hCtx
  | elim_forall _ A t _ ih =>
    intro D M v hΓ
    have hForall := ih D M v hΓ
    have hEval := hForall (evalTerm M v t)
    exact (eval_substFormula_zero M v t A).mpr hEval
  | intro_ex _ A t _ ih =>
    intro D M v hΓ
    have hA := ih D M v hΓ
    have hEval := (eval_substFormula_zero M v t A).mp hA
    exact ⟨evalTerm M v t, hEval⟩
  | elim_ex Γ' A B _ _ ih_ex ih_B =>
    intro D M v hΓ
    have hEx := ih_ex D M v hΓ
    obtain ⟨d, hd⟩ := hEx
    have hCtx : contextSatisfies M (shiftEnv v d) (A :: Γ'.map (liftFormula 0)) := by
      intro f' hf'
      cases hf' with
      | head _ => exact hd
      | tail _ hTail => exact (contextSatisfies_lift_zero M v d).mpr hΓ f' hTail
    have hB := ih_B D M (shiftEnv v d) hCtx
    exact (eval_liftFormula_zero M v d B).mp hB
  | rewrite_at _ _ _ _ sub sub' _ h_get h_rule h_replace ih =>
    intro D M v hΓ
    have hEvalF := ih D M v hΓ
    have hSubEq : ∀ v', evalFormula M v' sub ↔ evalFormula M v' sub' := fun v' => rule_soundness M v' h_rule
    have hEquiv := replaceAt_soundness M v h_get hSubEq
    rw [h_replace]
    exact hEquiv.mp hEvalF

end FOL.Metamath.Soundness

export FOL.Metamath.Soundness (soundness)
