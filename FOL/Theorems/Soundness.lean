/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL
import FOL.Semantics.Basic
import FOL.MetaTheory.Soundness

namespace FOL.Theorems.Soundness
open FOL.Metamath.Semantics

local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- Teorema de Corrección (Soundness) - Fase 5 (Opción B)
-- ============================================================
-- Demuestra que si Γ ⊢ f (sintácticamente demostrable), 
-- entonces Γ ⊨ f (semánticamente válido).
--
-- La demostración completa está en FOL.Soundness

theorem soundness {Γ f} (h : Γ ⊢ f) : Γ ⊨ f :=
  FOL.Metamath.Soundness.soundness h

end FOL.Theorems.Soundness
