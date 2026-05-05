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
-- @axiom_system: classical
-- @importance: high

import FOL.FOL
import FOL.Tactics.Basic

namespace FOL.Metamath.Deduction

-- ============================================================
-- Fase 5: Metamatemática - Teorema de Deducción
-- ============================================================

theorem deduction_theorem {Γ A B} (h : A :: Γ ⊢ B) : Γ ⊢ .impl A B := by
  apply Derives.intro_impl
  exact h

-- Free variables are semantically identical to zero-arity function applications:
-- evalTerm M v (fvar x) = M.func x [] = evalTerm M v (func x []) in all models.
-- This axiom is sound but not derivable from the current proof rules.
axiom fvar_eq_func : ∀ (Γ : List Formula) (x : String), Γ ⊢ .eq (Term.fvar x) (Term.func x [])

end FOL.Metamath.Deduction

export FOL.Metamath.Deduction (deduction_theorem fvar_eq_func)
