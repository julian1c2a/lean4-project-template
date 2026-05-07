import Lake
open Lake DSL

-- Replace «ProjectName» with your project name (must match directory name)
-- and update the package name accordingly
package «MyProject» where
  -- Disable auto-implicit to enforce explicit type annotations everywhere
  moreServerArgs := #["-DautoImplicit=false"]

-- ── External dependencies (uncomment as needed) ──────────────────────────────

-- ZfcSetTheory: ZFC set theory in Lean 4, no Mathlib
-- require ZfcSetTheory from git
--   "https://github.com/julian1c2a/ZfcSetTheory" @ "master"

-- Peano: Peano natural numbers, no Mathlib
-- require peanolib from git
--   "https://github.com/julian1c2a/Peano" @ "master"

-- FOL: First-Order Logic foundational library
-- require FOL from git
--   "https://github.com/julian1c2a/FOL" @ "master"

-- AczelSetTheory: Aczel's Anti-Foundation Axiom and non-well-founded sets
-- require AczelSetTheory from git
--   "https://github.com/julian1c2a/AczelSetTheory" @ "master"

-- Robinson: Robinson Arithmetic (Q)
-- require Robinson from git
--   "https://github.com/julian1c2a/Robinson" @ "master"

-- TG: Tarski-Grothendieck set theory
-- require TG from git
--   "https://github.com/julian1c2a/TG" @ "master"

-- MKplus: Morse-Kelley set theory (MK) with additions
-- require MKplus from git
--   "https://github.com/julian1c2a/MKplus" @ "master"

-- MathFoundations / yFoundations: General mathematical foundations
-- require MathFoundations from git
--   "https://github.com/julian1c2a/MathFoundations" @ "master"

-- Other dependency template:
-- require somedep from git
--   "https://github.com/user/repo" @ "main"

-- ─────────────────────────────────────────────────────────────────────────────

@[default_target]
lean_lib «MyProject» where

