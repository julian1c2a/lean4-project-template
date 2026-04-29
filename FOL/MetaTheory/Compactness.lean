/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Semantics, FOL.Soundness, FOL.Completeness
-- @axiom_system: classical
-- @importance: high

import FOL.FOL
import FOL.Semantics.Basic
import FOL.MetaTheory.Soundness
import FOL.MetaTheory.Completeness

namespace FOL.Metamath.Compacity

open FOL.Metamath.Semantics
open FOL.Metamath.Completeness
open FOL.Metamath.Soundness

-- ============================================================
-- Fase 5: Teorema de Compacidad (Compactness)
-- ============================================================

-- Todo conjunto satisfacible es sintácticamente consistente.
theorem consistency_of_satisfiable {S : Formula → Prop} (hSat : IsSatisfiable S) : IsConsistent S := by
  intro hBot
  obtain ⟨Γ, hΓ, hDer⟩ := hBot
  obtain ⟨D, M, v, hEval⟩ := hSat
  have hCtx : contextSatisfies M v Γ := fun f hf => hEval f (hΓ f hf)
  have hBotEval := soundness hDer D M v hCtx
  exact hBotEval

-- Un conjunto de fórmulas es satisfacible si y solo si todo subconjunto finito lo es.
theorem compactness_theorem (S : Formula → Prop) :
    IsSatisfiable S ↔ ∀ (Γ : List Formula), (∀ f, f ∈ Γ → S f) → IsSatisfiable (fun x => x ∈ Γ) := by
  apply Iff.intro
  · intro hSat Γ hSub
    obtain ⟨D, M, v, hEval⟩ := hSat
    exact ⟨D, M, v, fun f hf => hEval f (hSub f hf)⟩
  · intro hFinSat
    apply model_existence_lemma
    intro hBot
    obtain ⟨Γ, hΓ, hDer⟩ := hBot
    have hSatΓ := hFinSat Γ hΓ
    obtain ⟨D, M, v, hEvalΓ⟩ := hSatΓ
    exact soundness hDer D M v hEvalΓ

end FOL.Metamath.Compacity

export FOL.Metamath.Compacity (consistency_of_satisfiable compactness_theorem)
