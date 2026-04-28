/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: FOL.FOL, FOL.Semantics
-- @axiom_system: classical
-- @importance: high

import FOL.FOL
import FOL.Semantics.Basic
import FOL.ProofSystem.Deduction
import FOL.Theorems.Prop.Neg
import FOL.Theorems.FOL.Quantifiers

namespace FOL.Metamath.Completeness

open FOL.Metamath.Semantics
open Classical

-- DecidableEq se maneja mediante tacticas clásicas
-- local instance : DecidableEq Formula := Classical.decEq

local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

-- ============================================================
-- Fase 5: Teorema de Completitud (Completeness)
-- ============================================================

-- Para abordar la completitud (construcción de Henkin), necesitamos extender
-- las derivaciones desde contextos finitos (List) a conjuntos arbitrarios (Formula → Prop),
-- ya que un conjunto máximamente consistente es infinito.

def DerivesSet (S : Formula → Prop) (f : Formula) : Prop :=
  ∃ (Γ : List Formula), (∀ g, g ∈ Γ → S g) ∧ (Γ ⊢ f)

local notation:50 S " ⊢* " f => DerivesSet S f

def IsConsistent (S : Formula → Prop) : Prop :=
  ¬ (S ⊢* ⊥)

def IsMaximalConsistent (S : Formula → Prop) : Prop :=
  IsConsistent S ∧ ∀ f, ¬ S f → ¬ IsConsistent (fun x => S x ∨ x = f)

-- ============================================================
-- Propiedades Estructurales de DerivesSet
-- ============================================================

theorem DerivesSet_hyp {S : Formula → Prop} {f : Formula} (h : S f) : S ⊢* f := by
  apply Exists.intro ([f])
  constructor
  · intro g hg
    cases hg with
    | head _ => exact h
    | tail _ hTail => contradiction
  · apply Derives.hyp
    exact List.Mem.head _

theorem DerivesSet_weakening {S S' : Formula → Prop} {f : Formula}
    (h : S ⊢* f) (hSub : ∀ x, S x → S' x) : S' ⊢* f := by
  obtain ⟨Γ, hΓ, hDer⟩ := h
  apply Exists.intro (Γ)
  exact ⟨fun g hg => hSub g (hΓ g hg), hDer⟩

theorem DerivesSet_intro_impl {S : Formula → Prop} {A B : Formula}
    (h : (fun x => S x ∨ x = A) ⊢* B) : S ⊢* .impl A B := by
  obtain ⟨Γ, hΓ, hDer⟩ := h
  let Γ' := Γ.filter (fun x => x ≠ A)
  apply Exists.intro (Γ')
  constructor
  · intro g hg
    have h1 := List.mem_filter.mp hg
    have h2 := hΓ g h1.1
    cases h2 with
    | inl hS => exact hS
    | inr hEq => exfalso; exact of_decide_eq_true h1.2 hEq
  · apply FOL.Metamath.Deduction.deduction_theorem
    apply Derives.weakening _ _ _ hDer
    intro x hx
    by_cases heq : x = A
    · subst heq
      exact List.Mem.head _
    · apply List.Mem.tail
      apply List.mem_filter.mpr
      exact ⟨hx, decide_eq_true heq⟩

theorem DerivesSet_elim_impl {S : Formula → Prop} {A B : Formula}
    (hImpl : S ⊢* .impl A B) (hA : S ⊢* A) : S ⊢* B := by
  obtain ⟨Γ1, hΓ1, hDer1⟩ := hImpl
  obtain ⟨Γ2, hΓ2, hDer2⟩ := hA
  apply Exists.intro (Γ1 ++ Γ2)
  constructor
  · intro g hg
    have h_or := List.mem_append.mp hg
    cases h_or with
    | inl h1 => exact hΓ1 g h1
    | inr h2 => exact hΓ2 g h2
  · apply Derives.elim_impl (A := A)
    · apply Derives.weakening _ _ _ hDer1
      intro x hx
      apply List.mem_append.mpr
      exact Or.inl hx
    · apply Derives.weakening _ _ _ hDer2
      intro x hx
      apply List.mem_append.mpr
      exact Or.inr hx

-- ============================================================
-- Lema de Lindenbaum
-- ============================================================

-- Asumimos la enumerabilidad de las fórmulas
axiom formula_enum : Nat → Formula
axiom formula_enum_surj : ∀ f : Formula, ∃ n, formula_enum n = f

noncomputable def LindenbaumStep (S : Formula → Prop) : Nat → (Formula → Prop)
  | 0 => S
  | n + 1 =>
    let S_n := LindenbaumStep S n
    let f_n := formula_enum n
    if IsConsistent (fun x => S_n x ∨ x = f_n) then
      fun x => S_n x ∨ x = f_n
    else
      S_n

def LindenbaumLimit (S : Formula → Prop) (f : Formula) : Prop :=
  ∃ n, LindenbaumStep S n f

theorem lindenbaum_step_consistent {S : Formula → Prop} (hCons : IsConsistent S) (n : Nat) :
    IsConsistent (LindenbaumStep S n) := by
  induction n with
  | zero => exact hCons
  | succ n ih =>
    dsimp only [LindenbaumStep]
    split
    · rename_i h
      exact h
    · exact ih

theorem lindenbaum_step_subset {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : LindenbaumStep S n x) : LindenbaumStep S (n + 1) x := by
  dsimp only [LindenbaumStep]
  split
  · exact Or.inl h
  · exact h

theorem lindenbaum_step_mono {S : Formula → Prop} {n m : Nat} (hle : n ≤ m) {x : Formula}
    (hx : LindenbaumStep S n x) : LindenbaumStep S m x := by
  induction hle with
  | refl => exact hx
  | step _ ih => exact lindenbaum_step_subset _ ih

theorem lindenbaum_limit_bound {S : Formula → Prop} (Γ : List Formula)
    (hΓ : ∀ g ∈ Γ, LindenbaumLimit S g) : ∃ N, ∀ g ∈ Γ, LindenbaumStep S N g := by
  induction Γ with
  | nil =>
    apply Exists.intro (0)
    intro g hIn
    contradiction
  | cons g Γ' ih =>
    have hg_lim := hΓ g (List.Mem.head _)
    obtain ⟨n_g, hn_g⟩ := hg_lim
    have hΓ'_lim : ∀ g' ∈ Γ', LindenbaumLimit S g' := fun g' hg' => hΓ g' (List.Mem.tail _ hg')
    obtain ⟨N', hN'⟩ := ih hΓ'_lim
    apply Exists.intro (max n_g N')
    intro g' hg'
    cases hg' with
    | head _ =>
      have hLe : n_g ≤ max n_g N' := by omega
      exact lindenbaum_step_mono hLe hn_g
    | tail _ hTail =>
      have hLe : N' ≤ max n_g N' := by omega
      exact lindenbaum_step_mono hLe (hN' g' hTail)

-- Todo conjunto consistente puede extenderse a un conjunto máximamente consistente.
theorem lindenbaum_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ (∀ f, S f → S' f) := by
  apply Exists.intro (LindenbaumLimit S)
  constructor
  · constructor
    · -- Consistencia del límite (Compacidad sintáctica)
      intro hBot
      obtain ⟨Γ, hΓ, hDer⟩ := hBot
      have ⟨N, hN⟩ := lindenbaum_limit_bound Γ hΓ
      have hConsN := lindenbaum_step_consistent hCons N
      apply hConsN
      apply Exists.intro (Γ)
      exact ⟨hN, hDer⟩
    · -- Maximalidad del límite
      intro f hNotLim hConsExt
      obtain ⟨n, hn⟩ := formula_enum_surj f
      have hConsN : IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n) := by
        rw [hn]
        intro hBot
        apply hConsExt
        apply DerivesSet_weakening hBot
        intro x hx
        cases hx with
        | inl hStep => exact Or.inl ⟨n, hStep⟩
        | inr hEq => exact Or.inr hEq
      have hStep : LindenbaumStep S (n + 1) f := by
        dsimp only [LindenbaumStep]
        split
        · exact Or.inr hn.symm
        · contradiction
      exact hNotLim ⟨n + 1, hStep⟩
  · intro f hf
    exact ⟨0, hf⟩

-- ============================================================
-- Propiedades de Conjuntos Máximamente Consistentes
-- ============================================================

theorem max_cons_bot {S : Formula → Prop} (hMax : IsMaximalConsistent S) : ¬ S ⊥ := by
  intro h
  exact hMax.left (DerivesSet_hyp h)

mutual
theorem subst_lift_term_cancel (t : Term) (s : Term) (v : Nat) :
    substTerm v s (liftTerm v t) = t := by
  match t with
  | .bvar n =>
    dsimp [liftTerm, substTerm]
    split
    · rename_i h; simp [h]
    · rename_i h
      have h1 : ¬(n + 1 = v) := by omega
      have h2 : n + 1 > v := by omega
      have h3 : n + 1 - 1 = n := by omega
      simp [h1, h2, h3]
  | .fvar x => rfl
  | .func f ts =>
    dsimp [liftTerm, substTerm]
    congr 1
    exact subst_lift_terms_cancel ts s v

theorem subst_lift_terms_cancel (ts : List Term) (s : Term) (v : Nat) :
    substTerms v s (liftTerms v ts) = ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    dsimp [liftTerms, substTerms]
    congr 1
    · exact subst_lift_term_cancel t s v
    · exact subst_lift_terms_cancel ts' s v
end

theorem max_cons_eq_refl {S : Formula → Prop} (hMax : IsMaximalConsistent S) (t : Term) :
    S (.eq t t) := by
  apply max_cons_contains hMax
  apply Exists.intro ([])
  exact ⟨fun g hg => by contradiction, Derives.eq_refl [] t⟩

theorem max_cons_eq_symm {S : Formula → Prop} (hMax : IsMaximalConsistent S) {t1 t2 : Term}
    (h : S (.eq t1 t2)) : S (.eq t2 t1) := by
  obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp h
  apply max_cons_contains hMax
  apply Exists.intro (Γ)
  constructor
  · exact hΓ
  · let A := Formula.eq (.bvar 0) (liftTerm 0 t1)
    have hSubst1 : substFormula 0 t1 A = .eq t1 t1 := by
      dsimp [A, substFormula, substTerm]
      simp [subst_lift_term_cancel]
    have hSubst2 : substFormula 0 t2 A = .eq t2 t1 := by
      dsimp [A, substFormula, substTerm]
      simp [subst_lift_term_cancel]
    rw [← hSubst2]
    apply Derives.eq_subst Γ A t1 t2 hDer
    rw [hSubst1]
    exact Derives.eq_refl Γ t1

theorem max_cons_eq_trans {S : Formula → Prop} (hMax : IsMaximalConsistent S) {t1 t2 t3 : Term}
    (h12 : S (.eq t1 t2)) (h23 : S (.eq t2 t3)) : S (.eq t1 t3) := by
  obtain ⟨Γ1, hΓ1, hDer12⟩ := DerivesSet_hyp h12
  obtain ⟨Γ2, hΓ2, hDer23⟩ := DerivesSet_hyp h23
  apply max_cons_contains hMax
  apply Exists.intro (Γ1 ++ Γ2)
  constructor
  · intro g hg
    cases List.mem_append.mp hg with
    | inl h1 => exact hΓ1 g h1
    | inr h2 => exact hΓ2 g h2
  · let A := Formula.eq (liftTerm 0 t1) (.bvar 0)
    have hSubst2 : substFormula 0 t2 A = .eq t1 t2 := by
      dsimp [A, substFormula, substTerm]
      simp [subst_lift_term_cancel]
    have hSubst3 : substFormula 0 t3 A = .eq t1 t3 := by
      dsimp [A, substFormula, substTerm]
      simp [subst_lift_term_cancel]
    rw [← hSubst3]
    have hDer23_w := Derives.weakening Γ2 (Γ1 ++ Γ2) (.eq t2 t3) hDer23 (fun x hx => List.mem_append.mpr (Or.inr hx))
    have hDer12_w := Derives.weakening Γ1 (Γ1 ++ Γ2) (.eq t1 t2) hDer12 (fun x hx => List.mem_append.mpr (Or.inl hx))
    apply Derives.eq_subst (Γ1 ++ Γ2) A t2 t3 hDer23_w
    rw [hSubst2]
    exact hDer12_w

theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent S) {f : Formula} (h : S ⊢* f) : S f := by
  by_contra hNot
  have hInconsist : (fun x => S x ∨ x = f) ⊢* ⊥ := by
    by_contra hC
    exact hMax.right f hNot hC
  have hImpl : S ⊢* .impl f ⊥ := DerivesSet_intro_impl hInconsist
  have hBot : S ⊢* ⊥ := DerivesSet_elim_impl hImpl h
  exact hMax.left hBot

theorem max_cons_impl {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.impl A B) ↔ (S A → S B) := by
  constructor
  · intro hImpl hA
    exact max_cons_contains hMax (DerivesSet_elim_impl (DerivesSet_hyp hImpl) (DerivesSet_hyp hA))
  · intro hFn
    apply max_cons_contains hMax
    apply DerivesSet_intro_impl
    by_cases hA : S A
    · have hB := hFn hA
      apply DerivesSet_weakening (DerivesSet_hyp hB)
      intro x hx
      exact Or.inl hx
    · have hInconsist : (fun x => S x ∨ x = A) ⊢* ⊥ := by
        by_contra hC
        exact hMax.right A hA hC
      obtain ⟨Γ, hΓ, hDer⟩ := hInconsist
  apply Exists.intro (Γ)
      exact ⟨hΓ, Derives.bot_elim Γ B hDer⟩

theorem max_cons_and {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.and A B) ↔ (S A ∧ S B) := by
  constructor
  · intro hAnd
    obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hAnd
    have hA : S ⊢* A := ⟨Γ, hΓ, Derives.elim_and_l Γ A B hDer⟩
    have hB : S ⊢* B := ⟨Γ, hΓ, Derives.elim_and_r Γ A B hDer⟩
    exact ⟨max_cons_contains hMax hA, max_cons_contains hMax hB⟩
  · intro ⟨hA, hB⟩
    obtain ⟨Γ1, hΓ1, hDer1⟩ := DerivesSet_hyp hA
    obtain ⟨Γ2, hΓ2, hDer2⟩ := DerivesSet_hyp hB
    apply max_cons_contains hMax
  apply Exists.intro (Γ1 ++ Γ2)
    constructor
    · intro g hg
      cases List.mem_append.mp hg with
      | inl h1 => exact hΓ1 g h1
      | inr h2 => exact hΓ2 g h2
    · apply Derives.intro_and
      · apply Derives.weakening _ _ _ hDer1
        intro x hx; exact List.mem_append.mpr (Or.inl hx)
      · apply Derives.weakening _ _ _ hDer2
        intro x hx; exact List.mem_append.mpr (Or.inr hx)

theorem max_cons_or {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.or A B) ↔ (S A ∨ S B) := by
  constructor
  · intro hOr
    by_contra hNot
    have hNotA : ¬ S A := fun h => hNot (Or.inl h)
    have hNotB : ¬ S B := fun h => hNot (Or.inr h)
    have hInconsistA : (fun x => S x ∨ x = A) ⊢* ⊥ := by by_contra hC; exact hMax.right A hNotA hC
    have hInconsistB : (fun x => S x ∨ x = B) ⊢* ⊥ := by by_contra hC; exact hMax.right B hNotB hC
    obtain ⟨ΓOr, hΓOr, hDerOr⟩ := DerivesSet_hyp hOr
    obtain ⟨ΓA, hΓA, hDerA⟩ := DerivesSet_intro_impl hInconsistA
    obtain ⟨ΓB, hΓB, hDerB⟩ := DerivesSet_intro_impl hInconsistB
    have hBot : S ⊢* ⊥ := by
  apply Exists.intro (ΓOr ++ ΓA ++ ΓB)
      constructor
      · intro g hg
        cases List.mem_append.mp hg with
        | inl h1 => exact hΓOr g h1
        | inr h23 => cases List.mem_append.mp h23 with
          | inl h2 => exact hΓA g h2
          | inr h3 => exact hΓB g h3
      · apply Derives.elim_or (A := A) (B := B)
        · apply Derives.weakening _ _ _ hDerOr
          intro x hx; exact List.mem_append.mpr (Or.inl hx)
        · apply Derives.elim_impl (A := A) (B := .bottom)
          · apply Derives.weakening _ _ _ hDerA
            intro x hx; apply List.Mem.tail; apply List.mem_append.mpr; apply Or.inr; exact List.mem_append.mpr (Or.inl hx)
          · exact Derives.hyp _ _ (List.Mem.head _)
        · apply Derives.elim_impl (A := B) (B := .bottom)
          · apply Derives.weakening _ _ _ hDerB
            intro x hx; apply List.Mem.tail; apply List.mem_append.mpr; apply Or.inr; exact List.mem_append.mpr (Or.inr hx)
          · exact Derives.hyp _ _ (List.Mem.head _)
    exact hMax.left hBot
  · intro hOr
    cases hOr with
    | inl hA =>
      obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hA
      apply max_cons_contains hMax
  apply Exists.intro (Γ)
      exact ⟨hΓ, Derives.intro_or_l Γ A B hDer⟩
    | inr hB =>
      obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hB
      apply max_cons_contains hMax
  apply Exists.intro (Γ)
      exact ⟨hΓ, Derives.intro_or_r Γ A B hDer⟩

-- ============================================================
-- Modelo Canónico de Henkin
-- ============================================================

def termSetoid (S : Formula → Prop) (hMax : IsMaximalConsistent S) : Setoid Term where
  r t1 t2 := S (.eq t1 t2)
  iseqv := {
    refl := max_cons_eq_refl hMax
    symm := max_cons_eq_symm hMax
    trans := max_cons_eq_trans hMax
  }

def CanonicalDomain (S : Formula → Prop) (hMax : IsMaximalConsistent S) : Type :=
  Quotient (termSetoid S hMax)

noncomputable def canonicalFunc (S : Formula → Prop) (hMax : IsMaximalConsistent S)
    (f : String) (args : List (CanonicalDomain S hMax)) : CanonicalDomain S hMax :=
  let reps := args.map (fun q => Quotient.out q)
  Quotient.mk (termSetoid S hMax) (.func f reps)

noncomputable def canonicalRel (S : Formula → Prop) (hMax : IsMaximalConsistent S)
    (p : String) (args : List (CanonicalDomain S hMax)) : Prop :=
  let reps := args.map (fun q => Quotient.out q)
  S (.atom p reps)

noncomputable def canonicalModel (S : Formula → Prop) (hMax : IsMaximalConsistent S) : Model (CanonicalDomain S hMax) where
  func := canonicalFunc S hMax
  rel  := canonicalRel S hMax

noncomputable def canonicalEnv (S : Formula → Prop) (hMax : IsMaximalConsistent S) : Nat → CanonicalDomain S hMax :=
  fun n => Quotient.mk (termSetoid S hMax) (.bvar n)

theorem substTerms_append (v : Nat) (s : Term) (ts1 ts2 : List Term) :
    substTerms v s (ts1 ++ ts2) = substTerms v s ts1 ++ substTerms v s ts2 := by
  induction ts1 with
  | nil => rfl
  | cons t ts ih => simp only [List.append_eq, substTerms, ih, List.cons_append]

theorem max_cons_eq_subst {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A : Formula} {t1 t2 : Term}
    (hEq : S (.eq t1 t2)) (hA : S (substFormula 0 t1 A)) : S (substFormula 0 t2 A) := by
  obtain ⟨Γ1, hΓ1, hDer1⟩ := DerivesSet_hyp hEq
  obtain ⟨Γ2, hΓ2, hDer2⟩ := DerivesSet_hyp hA
  apply max_cons_contains hMax
  apply Exists.intro (Γ1 ++ Γ2)
  constructor
  · intro g hg
    cases List.mem_append.mp hg with
    | inl h1 => exact hΓ1 g h1
    | inr h2 => exact hΓ2 g h2
  · have hDer1_w := Derives.weakening Γ1 (Γ1 ++ Γ2) (.eq t1 t2) hDer1 (fun x hx => List.mem_append.mpr (Or.inl hx))
    have hDer2_w := Derives.weakening Γ2 (Γ1 ++ Γ2) (substFormula 0 t1 A) hDer2 (fun x hx => List.mem_append.mpr (Or.inr hx))
    exact Derives.eq_subst (Γ1 ++ Γ2) A t1 t2 hDer1_w hDer2_w

theorem max_cons_eq_func_step {S : Formula → Prop} (hMax : IsMaximalConsistent S) (f : String)
    (pre post : List Term) (t1 t2 : Term) (hEq : S (.eq t1 t2)) :
    S (.eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t2 :: post))) := by
  let A := Formula.eq (.func f (liftTerms 0 pre ++ liftTerm 0 t1 :: liftTerms 0 post))
                      (.func f (liftTerms 0 pre ++ .bvar 0 :: liftTerms 0 post))
  have hSubst1 : substFormula 0 t1 A = .eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t1 :: post)) := by
    dsimp [A, substFormula, substTerm]
    rw [substTerms_append, substTerms_append]
    simp [subst_lift_terms_cancel, subst_lift_term_cancel]
  have hSubst2 : substFormula 0 t2 A = .eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t2 :: post)) := by
    dsimp [A, substFormula, substTerm]
    rw [substTerms_append, substTerms_append]
    simp [subst_lift_terms_cancel, subst_lift_term_cancel]
  have hRefl := max_cons_eq_refl hMax (.func f (pre ++ t1 :: post))
  rw [← hSubst1] at hRefl
  have hDer := max_cons_eq_subst hMax hEq hRefl
  rw [hSubst2] at hDer
  exact hDer

theorem max_cons_eq_func_map {S : Formula → Prop} (hMax : IsMaximalConsistent S) (f : String)
    (ts : List Term) (pre : List Term) :
    S (.eq (.func f (pre ++ ts.map (fun t => Quotient.out (Quotient.mk (termSetoid S hMax) t))))
           (.func f (pre ++ ts))) := by
  induction ts generalizing pre with
  | nil =>
    simp only [List.map_nil, List.append_nil]
    exact max_cons_eq_refl hMax (.func f pre)
  | cons t ts' ih =>
    let t_out := Quotient.out (Quotient.mk (termSetoid S hMax) t)
    have hEq : S (.eq t_out t) := Quotient.exact (Quotient.out_eq (Quotient.mk (termSetoid S hMax) t))
    have hStep := max_cons_eq_func_step hMax f pre ts' t_out t hEq
    have hIH := ih (pre ++ [t_out])
    rw [List.append_assoc, List.append_assoc] at hIH
    exact max_cons_eq_trans hMax hIH hStep

mutual
theorem evalTerm_canonical (S : Formula → Prop) (hMax : IsMaximalConsistent S) (t : Term) :
    evalTerm (canonicalModel S hMax) (canonicalEnv S hMax) t = Quotient.mk (termSetoid S hMax) t := by
  match t with
  | .bvar n => rfl
  | .func f ts =>
    unfold evalTerm
    have ih := evalTerms_canonical S hMax ts
    rw [ih]
    unfold canonicalFunc
    apply Quotient.sound
    have hMap := max_cons_eq_func_map hMax f ts []
    simp only [List.nil_append] at hMap
    exact hMap

theorem evalTerms_canonical (S : Formula → Prop) (hMax : IsMaximalConsistent S) (ts : List Term) :
    evalTerms (canonicalModel S hMax) (canonicalEnv S hMax) ts = ts.map (Quotient.mk (termSetoid S hMax)) := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    unfold evalTerms
    have ih1 := evalTerm_canonical S hMax t
    have ih2 := evalTerms_canonical S hMax ts'
    rw [ih1, ih2]
    rfl
end

-- Un conjunto S tiene la propiedad de Henkin si contiene testigos para sus existenciales.
def IsHenkin (S : Formula → Prop) : Prop :=
  ∀ f, S (.ex f) → ∃ (t : Term), S (substFormula 0 t f)

def formulaComplexity : Formula → Nat
  | .bottom => 0
  | .eq _ _ => 0
  | .atom _ _ => 0
  | .impl f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .forall f1 => formulaComplexity f1 + 1
  | .and f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .or f1 f2 => max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .ex f1 => formulaComplexity f1 + 1

@[simp]
theorem complexity_substFormula (v : Nat) (t : Term) (f : Formula) :
    formulaComplexity (substFormula v t f) = formulaComplexity f := by
  induction f generalizing v t with
  | bottom => rfl
  | eq t1 t2 => rfl
  | atom p ts => rfl
  | impl f1 f2 ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | and f1 f2 ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | or f1 f2 ih1 ih2 => simp only [formulaComplexity, substFormula, ih1, ih2]
  | forall f1 ih => simp only [formulaComplexity, substFormula, ih]
  | ex f1 ih => simp only [formulaComplexity, substFormula, ih]

theorem max_cons_eq_atom_step {S : Formula → Prop} (hMax : IsMaximalConsistent S) (p : String)
    (pre post : List Term) (t1 t2 : Term) (hEq : S (.eq t1 t2)) :
    S (.atom p (pre ++ t1 :: post)) ↔ S (.atom p (pre ++ t2 :: post)) := by
  let A := Formula.atom p (liftTerms 0 pre ++ .bvar 0 :: liftTerms 0 post)
  have hSubst1 : substFormula 0 t1 A = .atom p (pre ++ t1 :: post) := by
    dsimp [A, substFormula, substTerm]
    rw [substTerms_append]
    simp [subst_lift_terms_cancel, subst_lift_term_cancel]
  have hSubst2 : substFormula 0 t2 A = .atom p (pre ++ t2 :: post) := by
    dsimp [A, substFormula, substTerm]
    rw [substTerms_append]
    simp [subst_lift_terms_cancel, subst_lift_term_cancel]
  constructor
  · intro h1
    have hA1 : S (substFormula 0 t1 A) := by rw [hSubst1]; exact h1
    have hA2 := max_cons_eq_subst hMax hEq hA1
    rw [hSubst2] at hA2
    exact hA2
  · intro h2
    have hEqSymm := max_cons_eq_symm hMax hEq
    have hA2 : S (substFormula 0 t2 A) := by rw [hSubst2]; exact h2
    have hA1 := max_cons_eq_subst hMax hEqSymm hA2
    rw [hSubst1] at hA1
    exact hA1

theorem max_cons_eq_atom_map {S : Formula → Prop} (hMax : IsMaximalConsistent S) (p : String)
    (ts : List Term) (pre : List Term) :
    S (.atom p (pre ++ ts.map (fun t => Quotient.out (Quotient.mk (termSetoid S hMax) t)))) ↔
    S (.atom p (pre ++ ts)) := by
  induction ts generalizing pre with
  | nil => simp only [List.map_nil, List.append_nil]
  | cons t ts' ih =>
    let t_out := Quotient.out (Quotient.mk (termSetoid S hMax) t)
    have hEq : S (.eq t_out t) := Quotient.exact (Quotient.out_eq (Quotient.mk (termSetoid S hMax) t))
    have hStep := max_cons_eq_atom_step hMax p pre ts' t_out t hEq
    have hIH := ih (pre ++ [t_out])
    rw [List.append_assoc, List.append_assoc] at hIH
    exact Iff.trans hIH hStep

theorem max_cons_ex {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S) {A : Formula} :
    S (.ex A) ↔ ∃ t, S (substFormula 0 t A) := by
  constructor
  · intro hEx
    exact hHenkin A hEx
  · intro ⟨t, ht⟩
    apply max_cons_contains hMax
  apply Exists.intro ([substFormula 0 t A])
    constructor
    · intro g hg
      cases hg with
      | head _ => exact ht
      | tail _ hTail => contradiction
    · apply Derives.intro_ex
      apply Derives.hyp
      exact List.Mem.head _

theorem max_cons_forall {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S) {A : Formula} :
    S (.forall A) ↔ ∀ t, S (substFormula 0 t A) := by
  constructor
  · intro hAll t
    apply max_cons_contains hMax
  apply Exists.intro ([.forall A])
    constructor
    · intro g hg
      cases hg with
      | head _ => exact hAll
      | tail _ hTail => contradiction
    · apply Derives.elim_forall
      apply Derives.hyp
      exact List.Mem.head _
  · intro hAll
    by_contra hNotAll
    have hInconsist : (fun x => S x ∨ x = .forall A) ⊢* ⊥ := by
      by_contra hC; exact hMax.right (.forall A) hNotAll hC
    have hNegForall : S ⊢* neg (.forall A) := DerivesSet_intro_impl hInconsist
    have hExNeg_impl : S ⊢* .impl (neg (.forall A)) (.ex (neg A)) := by
  apply Exists.intro ([])
      constructor
      · intro g hg; contradiction
      · exact FOL.Theorems.FOL.Quantifiers.forall_not_impl_exists_not
    have hExNeg : S ⊢* .ex (neg A) := DerivesSet_elim_impl hExNeg_impl hNegForall
    have hS_ExNeg : S (.ex (neg A)) := max_cons_contains hMax hExNeg
    obtain ⟨t, ht⟩ := hHenkin (neg A) hS_ExNeg
    have hS_NegA : S (neg (substFormula 0 t A)) := ht
    have hS_A : S (substFormula 0 t A) := hAll t
    have hBot : S ⊢* ⊥ := by
  apply Exists.intro ([neg (substFormula 0 t A), substFormula 0 t A])
      constructor
      · intro g hg
        cases hg with
        | head _ => exact hS_NegA
        | tail _ hTail =>
          cases hTail with
          | head _ => exact hS_A
          | tail _ hT => contradiction
      · apply Derives.elim_impl (A := substFormula 0 t A) (B := .bottom)
        · apply Derives.hyp; exact List.Mem.head _
        · apply Derives.hyp; exact List.Mem.tail _ (List.Mem.head _)
    exact hMax.left hBot

theorem truth_lemma_aux {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S)
    (n : Nat) (f : Formula) (hEq : formulaComplexity f = n) :
    evalFormula (canonicalModel S) canonicalEnv f ↔ S f := by
  induction n using Nat.strongInductionOn generalizing f with
  | ind n ih =>
    cases f with
    | bottom =>
      simp only [evalFormula]
      apply Iff.intro
      · intro h; contradiction
      · exact max_cons_bot hMax
    | eq t1 t2 =>
      simp only [evalFormula]
      have hEval1 := evalTerm_canonical S hMax t1
      have hEval2 := evalTerm_canonical S hMax t2
      rw [hEval1, hEval2]
      exact Quotient.eq (r := termSetoid S hMax)
    | atom p ts =>
      simp only [evalFormula]
      have hEval := evalTerms_canonical S hMax ts
      rw [hEval]
      unfold canonicalRel
      have hMap := max_cons_eq_atom_map hMax p ts []
      simp only [List.nil_append] at hMap
      exact hMap
    | impl f1 f2 =>
      have ih1 := ih (formulaComplexity f1) (by omega) f1 rfl
      have ih2 := ih (formulaComplexity f2) (by omega) f2 rfl
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_impl hMax).symm
    | and f1 f2 =>
      have ih1 := ih (formulaComplexity f1) (by omega) f1 rfl
      have ih2 := ih (formulaComplexity f2) (by omega) f2 rfl
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_and hMax).symm
    | or f1 f2 =>
      have ih1 := ih (formulaComplexity f1) (by omega) f1 rfl
      have ih2 := ih (formulaComplexity f2) (by omega) f2 rfl
      simp only [evalFormula]
      rw [ih1, ih2]
      exact (max_cons_or hMax).symm
    | forall f1 =>
      simp only [evalFormula]
      have h_eq : (∀ d : CanonicalDomain S hMax, evalFormula (canonicalModel S hMax) (shiftEnv (canonicalEnv S hMax) d) f1) ↔
                  (∀ t : Term, S (substFormula 0 t f1)) := by
        apply Iff.intro
        · intro h t
          have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
          rw [evalTerm_canonical S hMax t] at hSubst
          have hEval := hSubst.symm.mp (h (Quotient.mk (termSetoid S hMax) t))
          exact (ih (formulaComplexity f1) (by omega) (substFormula 0 t f1) (by simp)).mp hEval
        · intro h d
          obtain ⟨t, ht⟩ := Quotient.exists_rep d
          subst ht
          have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
          rw [evalTerm_canonical S hMax t] at hSubst
          have hEval := (ih (formulaComplexity f1) (by omega) (substFormula 0 t f1) (by simp)).mpr (h t)
          exact hSubst.mpr hEval
      rw [h_eq]
      exact (max_cons_forall hMax hHenkin).symm
    | ex f1 =>
      simp only [evalFormula]
      have h_eq : (∃ d : CanonicalDomain S hMax, evalFormula (canonicalModel S hMax) (shiftEnv (canonicalEnv S hMax) d) f1) ↔
                  (∃ t : Term, S (substFormula 0 t f1)) := by
        apply Iff.intro
        · intro ⟨d, hd⟩
          obtain ⟨t, ht⟩ := Quotient.exists_rep d
          subst ht
          have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
          rw [evalTerm_canonical S hMax t] at hSubst
          have hEval := hSubst.symm.mp hd
          exact ⟨t, (ih (formulaComplexity f1) (by omega) (substFormula 0 t f1) (by simp)).mp hEval⟩
        · intro ⟨t, ht⟩
          have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
          rw [evalTerm_canonical S hMax t] at hSubst
          have hEval := (ih (formulaComplexity f1) (by omega) (substFormula 0 t f1) (by simp)).mpr ht
          exact ⟨Quotient.mk (termSetoid S hMax) t, hSubst.mpr hEval⟩
      rw [h_eq]
      exact (max_cons_ex hMax hHenkin).symm

-- Lema de la Verdad (Truth Lemma): La semántica coincide con la sintaxis en el modelo canónico.
theorem truth_lemma {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S) (f : Formula) :
    evalFormula (canonicalModel S hMax) (canonicalEnv S hMax) f ↔ S f :=
  truth_lemma_aux hMax hHenkin (formulaComplexity f) f rfl

-- ============================================================
-- Extensión de Henkin
-- ============================================================

-- Todo conjunto consistente puede extenderse a uno máximamente consistente
-- que además contenga testigos para sus fórmulas existenciales.
-- (Su demostración constructiva requiere expandir el lenguaje con constantes).
axiom henkin_extension_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ IsHenkin S' ∧ (∀ f, S f → S' f)

def IsSatisfiable (S : Formula → Prop) : Prop :=
  ∃ (D : Type) (M : Model D) (v : Nat → D), ∀ f, S f → evalFormula M v f

theorem model_existence_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    IsSatisfiable S := by
  obtain ⟨S', hMax, hHenkin, hSub⟩ := henkin_extension_lemma hCons
  apply Exists.intro (CanonicalDomain S' hMax, canonicalModel S' hMax, canonicalEnv S' hMax)
  intro f hf
  exact (truth_lemma hMax hHenkin f).mpr (hSub f hf)

-- El Teorema de Completitud (Objetivo Final)
theorem completeness {Γ : List Formula} {f : Formula} (h : Γ ⊨ f) : Γ ⊢ f := by
  by_contra hNotDerive
  let S : Formula → Prop := fun x => x ∈ Γ ∨ x = neg f
  have hCons : IsConsistent S := by
    intro hBot
    have hInconsist : (fun x => (fun y => y ∈ Γ) x ∨ x = neg f) ⊢* ⊥ := hBot
    have hImpl : (fun y => y ∈ Γ) ⊢* .impl (neg f) ⊥ := DerivesSet_intro_impl hInconsist
    obtain ⟨Γ_sub, hΓ_sub, hDer_impl⟩ := hImpl
    have hDNE : Γ_sub ⊢ .impl (neg (neg f)) f := FOL.Theorems.Prop.Neg.double_neg_elim
    have hDer_f : Γ_sub ⊢ f := Derives.elim_impl Γ_sub (neg (neg f)) f hDNE hDer_impl
    have hDer_Γ : Γ ⊢ f := Derives.weakening Γ_sub Γ f hDer_f hΓ_sub
    exact hNotDerive hDer_Γ

  obtain ⟨D, M, v, hModel⟩ := model_existence_lemma hCons
  have hSat : contextSatisfies M v Γ := by
    intro g hg
    exact hModel g (Or.inl hg)
  have hEval_f : evalFormula M v f := h D M v hSat
  have hEval_neg_f : evalFormula M v (neg f) := hModel (neg f) (Or.inr rfl)
  exact hEval_neg_f hEval_f

end FOL.Metamath.Completeness

export FOL.Metamath.Completeness (
  DerivesSet
  IsConsistent
  IsMaximalConsistent
  IsSatisfiable
  model_existence_lemma
  completeness
)
