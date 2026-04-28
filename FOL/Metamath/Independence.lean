/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.ProofSystem.Deduction

namespace FOL.Metamath

/-!
# Independence

This module defines when a formula is independent of a given theory.
-/

/-- A formula φ is independent of a theory Γ if neither φ nor ¬φ can be derived from Γ. -/
def Independent (Γ : List Formula) (φ : Formula) : Prop :=
  And (Not (Γ ⊢ φ)) (Not (Γ ⊢ neg φ))

end FOL.Metamath
