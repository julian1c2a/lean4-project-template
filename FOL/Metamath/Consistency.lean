/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.ProofSystem.Deduction

namespace FOL.Metamath

/-!
# Consistency

This module defines the concept of consistency for a set of formulas
(a theory) in our first-order logic framework.
-/

/-- A theory Γ is consistent if it does not derive contradiction (⊥). -/
def Consistent (Γ : List Formula) : Prop :=
  ¬ (Γ ⊢ ⊥)

end FOL.Metamath
