/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import FOL.FOL
import FOL.Semantics.Basic
import FOL.ProofSystem.Deduction
import FOL.Theorems.Prop.Neg
import FOL.Theorems.FOL.Quantifiers

namespace FOL.Metamath.Completeness

open FOL.Metamath.Semantics
open Classical

local notation:50 Γ " ⊨ " f => FOL.Metamath.Semantics.satisfies Γ f

def DerivesSet (S : Formula → Prop) (f : Formula) : Prop :=
  ∃ (Γ : List Formula), (∀ g, g ∈ Γ → S g) ∧ (Γ ⊢ f)

local notation:50 S " ⊢* " f => DerivesSet S f

def IsConsistent (S : Formula → Prop) : Prop := ¬ (S ⊢* ⊥)

def IsMaximalConsistent (S : Formula → Prop) : Prop :=
  IsConsistent S ∧ ∀ f, ¬ S f → ¬ IsConsistent (fun x => S x ∨ x = f)

-- Classical Double Negation Elimination as an axiom in the proof system
axiom classical_dne : ∀ (Γ : List Formula) (A : Formula), Γ ⊢ .impl (neg (neg A)) A

-- ============================================================
-- Propiedades estructurales de DerivesSet
-- ============================================================

theorem DerivesSet_hyp {S : Formula → Prop} {f : Formula} (h : S f) : S ⊢* f :=
  ⟨[f], fun g hg => by
    cases hg with
    | head _ => exact h
    | tail _ ht => exact (List.not_mem_nil ht).elim,
   Derives.hyp _ _ (List.Mem.head _)⟩

theorem DerivesSet_weakening {S S' : Formula → Prop} {f : Formula}
    (h : S ⊢* f) (hSub : ∀ x, S x → S' x) : S' ⊢* f :=
  let ⟨Γ, hΓ, hDer⟩ := h; ⟨Γ, fun g hg => hSub g (hΓ g hg), hDer⟩

theorem DerivesSet_intro_impl' {S : Formula → Prop} {A B : Formula}
    (h : (fun x => S x ∨ x = A) ⊢* B) : S ⊢* .impl A B := by
  obtain ⟨Γ, hΓ, hDer⟩ := h
  refine ⟨Γ.filter (fun x => x ≠ A), ?_, ?_⟩
  · intro g hg
    have h1 := List.mem_filter.mp hg
    rcases hΓ g h1.1 with hS | hEq
    · exact hS
    · simp [hEq] at h1
  · exact FOL.Metamath.Deduction.deduction_theorem (Derives.weakening _ _ _ hDer (fun x hx => by
      by_cases heq : x = A
      · exact heq ▸ List.Mem.head _
      · exact List.Mem.tail _ (List.mem_filter.mpr ⟨hx, decide_eq_true heq⟩)))

theorem DerivesSet_elim_impl {S : Formula → Prop} {A B : Formula}
    (hImpl : S ⊢* .impl A B) (hA : S ⊢* A) : S ⊢* B :=
  let ⟨Γ1, hΓ1, hDer1⟩ := hImpl
  let ⟨Γ2, hΓ2, hDer2⟩ := hA
  ⟨Γ1 ++ Γ2,
   fun g hg => by rcases List.mem_append.mp hg with h1 | h2
                  · exact hΓ1 g h1
                  · exact hΓ2 g h2,
   Derives.elim_impl _ A B
     (Derives.weakening _ _ _ hDer1 (fun x hx => List.mem_append.mpr (Or.inl hx)))
     (Derives.weakening _ _ _ hDer2 (fun x hx => List.mem_append.mpr (Or.inr hx)))⟩

-- ============================================================
-- Lema de Lindenbaum
-- ============================================================

axiom formula_enum : Nat → Formula
axiom formula_enum_surj : ∀ f : Formula, ∃ n, formula_enum n = f

noncomputable def LindenbaumStep (S : Formula → Prop) : Nat → (Formula → Prop)
  | 0 => S
  | n + 1 =>
    if IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n) then
      fun x => LindenbaumStep S n x ∨ x = formula_enum n
    else LindenbaumStep S n

def LindenbaumLimit (S : Formula → Prop) (f : Formula) : Prop := ∃ n, LindenbaumStep S n f

theorem lindenbaum_step_consistent {S : Formula → Prop} (hCons : IsConsistent S) :
    ∀ n, IsConsistent (LindenbaumStep S n)
  | 0 => hCons
  | n + 1 => by
      simp only [LindenbaumStep]; split
      · rename_i h; exact h
      · exact lindenbaum_step_consistent hCons n

theorem lindenbaum_step_subset {S : Formula → Prop} (n : Nat) {x : Formula}
    (h : LindenbaumStep S n x) : LindenbaumStep S (n + 1) x := by
  simp only [LindenbaumStep]; split
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
  | nil => exact ⟨0, fun _ h => (List.not_mem_nil h).elim⟩
  | cons g Γ' ih =>
    obtain ⟨n_g, hn_g⟩ := hΓ g (List.Mem.head _)
    obtain ⟨N', hN'⟩ := ih (fun g' hg' => hΓ g' (List.Mem.tail _ hg'))
    exact ⟨max n_g N', fun g' hg' => by
      cases hg' with
      | head _ => exact lindenbaum_step_mono (Nat.le_max_left _ _) hn_g
      | tail _ hTail => exact lindenbaum_step_mono (Nat.le_max_right _ _) (hN' g' hTail)⟩

theorem lindenbaum_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ (∀ f, S f → S' f) := by
  refine ⟨LindenbaumLimit S, ⟨?_, ?_⟩, fun f hf => ⟨0, hf⟩⟩
  · intro hBot
    obtain ⟨Γ, hΓ, hDer⟩ := hBot
    obtain ⟨N, hN⟩ := lindenbaum_limit_bound Γ hΓ
    exact lindenbaum_step_consistent hCons N ⟨Γ, hN, hDer⟩
  · intro f hNotLim hConsExt
    obtain ⟨n, hn⟩ := formula_enum_surj f
    have hConsN : IsConsistent (fun x => LindenbaumStep S n x ∨ x = formula_enum n) := by
      rw [hn]; intro hBot; apply hConsExt
      exact DerivesSet_weakening hBot (fun x hx => by
        rcases hx with hStep | hEq
        · exact Or.inl ⟨n, hStep⟩
        · exact Or.inr hEq)
    have hStep : LindenbaumStep S (n + 1) f := by
      simp only [LindenbaumStep]; split
      · exact Or.inr hn.symm
      · contradiction
    exact hNotLim ⟨n + 1, hStep⟩

-- ============================================================
-- Propiedades de Conjuntos Máximamente Consistentes
-- ============================================================

theorem max_cons_bot {S : Formula → Prop} (hMax : IsMaximalConsistent S) : ¬ S ⊥ :=
  fun h => hMax.left (DerivesSet_hyp h)

theorem max_cons_contains {S : Formula → Prop} (hMax : IsMaximalConsistent S) {f : Formula}
    (h : S ⊢* f) : S f :=
  byContradiction fun hNot =>
    hMax.left (DerivesSet_elim_impl
      (DerivesSet_intro_impl' (byContradiction fun hC => hMax.right f hNot hC)) h)

-- Cancellation: substTerm v s (liftTerm v t) = t
mutual
theorem subst_lift_term_cancel (t s : Term) (v : Nat) : substTerm v s (liftTerm v t) = t := by
  match t with
  | .bvar n =>
    by_cases h : n < v
    · have hne : n ≠ v := Nat.ne_of_lt h
      have hlt : ¬(n > v) := Nat.not_lt.mpr (Nat.le_of_lt h)
      simp [liftTerm, substTerm, h, hne, hlt]
    · have hgt : n + 1 > v := by omega
      have hne : n + 1 ≠ v := by omega
      have heq : n + 1 - 1 = n := by omega
      simp [liftTerm, substTerm, h, hgt, hne, heq]
  | .fvar x => rfl
  | .func f ts =>
    simp only [liftTerm, substTerm]; congr 1
    exact subst_lift_terms_cancel ts s v

theorem subst_lift_terms_cancel (ts : List Term) (s : Term) (v : Nat) :
    substTerms v s (liftTerms v ts) = ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    simp only [liftTerms, substTerms]
    congr 1
    · exact subst_lift_term_cancel t s v
    · exact subst_lift_terms_cancel ts' s v
end

theorem max_cons_eq_refl {S : Formula → Prop} (hMax : IsMaximalConsistent S) (t : Term) :
    S (.eq t t) :=
  max_cons_contains hMax ⟨[], fun _ h => (List.not_mem_nil h).elim, Derives.eq_refl [] t⟩

theorem max_cons_eq_symm {S : Formula → Prop} (hMax : IsMaximalConsistent S) {t1 t2 : Term}
    (h : S (.eq t1 t2)) : S (.eq t2 t1) := by
  obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp h
  apply max_cons_contains hMax
  refine ⟨Γ, hΓ, ?_⟩
  let A := Formula.eq (.bvar 0) (liftTerm 0 t1)
  have hA1 : substFormula 0 t1 A = .eq t1 t1 := by
    simp [A, substFormula, substTerm, subst_lift_term_cancel]
  have hA2 : substFormula 0 t2 A = .eq t2 t1 := by
    simp [A, substFormula, substTerm, subst_lift_term_cancel]
  rw [← hA2]
  exact Derives.eq_subst Γ A t1 t2 hDer (hA1 ▸ Derives.eq_refl Γ t1)

theorem max_cons_eq_trans {S : Formula → Prop} (hMax : IsMaximalConsistent S) {t1 t2 t3 : Term}
    (h12 : S (.eq t1 t2)) (h23 : S (.eq t2 t3)) : S (.eq t1 t3) := by
  obtain ⟨Γ1, hΓ1, hDer12⟩ := DerivesSet_hyp h12
  obtain ⟨Γ2, hΓ2, hDer23⟩ := DerivesSet_hyp h23
  apply max_cons_contains hMax
  refine ⟨Γ1 ++ Γ2, fun g hg => ?_, ?_⟩
  · rcases List.mem_append.mp hg with h1 | h2
    · exact hΓ1 g h1
    · exact hΓ2 g h2
  · let A := Formula.eq (liftTerm 0 t1) (.bvar 0)
    have hA2 : substFormula 0 t2 A = .eq t1 t2 := by
      simp [A, substFormula, substTerm, subst_lift_term_cancel]
    have hA3 : substFormula 0 t3 A = .eq t1 t3 := by
      simp [A, substFormula, substTerm, subst_lift_term_cancel]
    rw [← hA3]
    exact Derives.eq_subst _ A t2 t3
      (Derives.weakening _ _ _ hDer23 (fun x hx => List.mem_append.mpr (Or.inr hx)))
      (hA2 ▸ Derives.weakening _ _ _ hDer12 (fun x hx => List.mem_append.mpr (Or.inl hx)))

theorem max_cons_impl {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.impl A B) ↔ (S A → S B) := by
  constructor
  · intro hImpl hA
    exact max_cons_contains hMax (DerivesSet_elim_impl (DerivesSet_hyp hImpl) (DerivesSet_hyp hA))
  · intro hFn
    apply max_cons_contains hMax
    apply DerivesSet_intro_impl'
    rcases Classical.em (S A) with hA | hA
    · exact DerivesSet_weakening (DerivesSet_hyp (hFn hA)) (fun x hx => Or.inl hx)
    · have hInc : (fun x => S x ∨ x = A) ⊢* ⊥ :=
        byContradiction fun hC => hMax.right A hA hC
      obtain ⟨Γ, hΓ, hDer⟩ := hInc
      exact ⟨Γ, hΓ, Derives.bot_elim Γ B hDer⟩

theorem max_cons_and {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.and A B) ↔ (S A ∧ S B) := by
  constructor
  · intro hAnd
    obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hAnd
    exact ⟨max_cons_contains hMax ⟨Γ, hΓ, Derives.elim_and_l Γ A B hDer⟩,
           max_cons_contains hMax ⟨Γ, hΓ, Derives.elim_and_r Γ A B hDer⟩⟩
  · intro ⟨hA, hB⟩
    obtain ⟨Γ1, hΓ1, hDer1⟩ := DerivesSet_hyp hA
    obtain ⟨Γ2, hΓ2, hDer2⟩ := DerivesSet_hyp hB
    apply max_cons_contains hMax
    refine ⟨Γ1 ++ Γ2, fun g hg => ?_, ?_⟩
    · rcases List.mem_append.mp hg with h1 | h2
      · exact hΓ1 g h1
      · exact hΓ2 g h2
    · exact Derives.intro_and (Γ1 ++ Γ2) A B
        (Derives.weakening _ _ _ hDer1 (fun x hx => List.mem_append.mpr (Or.inl hx)))
        (Derives.weakening _ _ _ hDer2 (fun x hx => List.mem_append.mpr (Or.inr hx)))

theorem max_cons_or {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A B : Formula} :
    S (.or A B) ↔ (S A ∨ S B) := by
  constructor
  · intro hOr
    rcases Classical.em (S A) with hA | hNotA
    · exact Or.inl hA
    · rcases Classical.em (S B) with hB | hNotB
      · exact Or.inr hB
      · exfalso
        have hIA : (fun x => S x ∨ x = A) ⊢* ⊥ :=
          byContradiction fun hC => hMax.right A hNotA hC
        have hIB : (fun x => S x ∨ x = B) ⊢* ⊥ :=
          byContradiction fun hC => hMax.right B hNotB hC
        obtain ⟨ΓOr, hΓOr, hDerOr⟩ := DerivesSet_hyp hOr
        obtain ⟨ΓA, hΓA, hDerA⟩ := DerivesSet_intro_impl' hIA
        obtain ⟨ΓB, hΓB, hDerB⟩ := DerivesSet_intro_impl' hIB
        apply hMax.left
        refine ⟨ΓOr ++ ΓA ++ ΓB, fun g hg => ?_, ?_⟩
        · rcases List.mem_append.mp hg with h12 | h3
          · rcases List.mem_append.mp h12 with h1 | h2
            · exact hΓOr g h1
            · exact hΓA g h2
          · exact hΓB g h3
        · apply Derives.elim_or (A := A) (B := B)
          · exact Derives.weakening _ _ _ hDerOr
              (fun x hx => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx))))
          · apply Derives.elim_impl _ A .bottom
            · exact Derives.weakening _ _ _ hDerA
                (fun x hx => List.Mem.tail _
                  (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))))
            · exact Derives.hyp _ _ (List.Mem.head _)
          · apply Derives.elim_impl _ B .bottom
            · exact Derives.weakening _ _ _ hDerB
                (fun x hx => List.Mem.tail _ (List.mem_append.mpr (Or.inr hx)))
            · exact Derives.hyp _ _ (List.Mem.head _)
  · intro hOr
    rcases hOr with hA | hB
    · obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hA
      exact max_cons_contains hMax ⟨Γ, hΓ, Derives.intro_or_l Γ A B hDer⟩
    · obtain ⟨Γ, hΓ, hDer⟩ := DerivesSet_hyp hB
      exact max_cons_contains hMax ⟨Γ, hΓ, Derives.intro_or_r Γ A B hDer⟩

-- ============================================================
-- Modelo Canónico de Henkin
-- ============================================================

def termSetoid (S : Formula → Prop) (hMax : IsMaximalConsistent S) : Setoid Term where
  r t1 t2 := S (.eq t1 t2)
  iseqv := ⟨max_cons_eq_refl hMax, max_cons_eq_symm hMax, max_cons_eq_trans hMax⟩

def CanonicalDomain (S : Formula → Prop) (hMax : IsMaximalConsistent S) : Type :=
  Quotient (termSetoid S hMax)

-- Quotient.out is not in Lean 4 core without Mathlib
noncomputable def quotientOut {α : Type} {s : Setoid α} (q : Quotient s) : α :=
  (Quotient.exists_rep q).choose

theorem quotientOut_eq {α : Type} {s : Setoid α} (q : Quotient s) :
    Quotient.mk s (quotientOut q) = q :=
  (Quotient.exists_rep q).choose_spec

noncomputable def canonicalFunc (S : Formula → Prop) (hMax : IsMaximalConsistent S)
    (f : String) (args : List (CanonicalDomain S hMax)) : CanonicalDomain S hMax :=
  Quotient.mk (termSetoid S hMax) (.func f (args.map quotientOut))

noncomputable def canonicalRel (S : Formula → Prop) (hMax : IsMaximalConsistent S)
    (p : String) (args : List (CanonicalDomain S hMax)) : Prop :=
  S (.atom p (args.map quotientOut))

noncomputable def canonicalModel (S : Formula → Prop) (hMax : IsMaximalConsistent S) :
    Model (CanonicalDomain S hMax) :=
  { func := canonicalFunc S hMax, rel := canonicalRel S hMax }

noncomputable def canonicalEnv (S : Formula → Prop) (hMax : IsMaximalConsistent S) :
    Nat → CanonicalDomain S hMax :=
  fun n => Quotient.mk (termSetoid S hMax) (.bvar n)

theorem substTerms_append (v : Nat) (s : Term) (ts1 ts2 : List Term) :
    substTerms v s (ts1 ++ ts2) = substTerms v s ts1 ++ substTerms v s ts2 := by
  induction ts1 with
  | nil => rfl
  | cons t ts ih => simp only [substTerms, List.cons_append, ih]

theorem substTerms_bvar_zero_cons (s : Term) (ts : List Term) :
    substTerms 0 s (.bvar 0 :: liftTerms 0 ts) = s :: ts := by
  simp [substTerms, substTerm, subst_lift_terms_cancel]

theorem substTerms_lifted_cons (s t : Term) (ts : List Term) :
    substTerms 0 s (liftTerm 0 t :: liftTerms 0 ts) = t :: ts := by
  simp [substTerms, subst_lift_term_cancel, subst_lift_terms_cancel]

theorem max_cons_eq_subst {S : Formula → Prop} (hMax : IsMaximalConsistent S) {A : Formula}
    {t1 t2 : Term} (hEq : S (.eq t1 t2)) (hA : S (substFormula 0 t1 A)) :
    S (substFormula 0 t2 A) := by
  obtain ⟨Γ1, hΓ1, hDer1⟩ := DerivesSet_hyp hEq
  obtain ⟨Γ2, hΓ2, hDer2⟩ := DerivesSet_hyp hA
  exact max_cons_contains hMax ⟨Γ1 ++ Γ2,
    fun g hg => by rcases List.mem_append.mp hg with h1 | h2
                   · exact hΓ1 g h1
                   · exact hΓ2 g h2,
    Derives.eq_subst _ A t1 t2
      (Derives.weakening _ _ _ hDer1 (fun x hx => List.mem_append.mpr (Or.inl hx)))
      (Derives.weakening _ _ _ hDer2 (fun x hx => List.mem_append.mpr (Or.inr hx)))⟩

theorem max_cons_eq_func_step {S : Formula → Prop} (hMax : IsMaximalConsistent S) (f : String)
    (pre post : List Term) (t1 t2 : Term) (hEq : S (.eq t1 t2)) :
    S (.eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t2 :: post))) := by
  let A := Formula.eq (.func f (liftTerms 0 pre ++ liftTerm 0 t1 :: liftTerms 0 post))
                      (.func f (liftTerms 0 pre ++ .bvar 0 :: liftTerms 0 post))
  have hSLC_pre := subst_lift_terms_cancel pre t1 0
  have hSLC_pre2 := subst_lift_terms_cancel pre t2 0
  have h1 : substTerms 0 t1 (liftTerm 0 t1 :: liftTerms 0 post) = t1 :: post :=
    substTerms_lifted_cons t1 t1 post
  have h2 : substTerms 0 t1 (.bvar 0 :: liftTerms 0 post) = t1 :: post :=
    substTerms_bvar_zero_cons t1 post
  have h3 : substTerms 0 t2 (liftTerm 0 t1 :: liftTerms 0 post) = t1 :: post := by
    simp [substTerms, subst_lift_term_cancel, subst_lift_terms_cancel]
  have h4 : substTerms 0 t2 (.bvar 0 :: liftTerms 0 post) = t2 :: post :=
    substTerms_bvar_zero_cons t2 post
  have hSubst1 : substFormula 0 t1 A =
      .eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t1 :: post)) := by
    simp only [A, substFormula, substTerm, substTerms_append, hSLC_pre, h1, h2]
  have hSubst2 : substFormula 0 t2 A =
      .eq (.func f (pre ++ t1 :: post)) (.func f (pre ++ t2 :: post)) := by
    simp only [A, substFormula, substTerm, substTerms_append, hSLC_pre2, h3, h4]
  rw [← hSubst2]
  exact max_cons_eq_subst hMax hEq (hSubst1 ▸ max_cons_eq_refl hMax _)

theorem max_cons_eq_func_map {S : Formula → Prop} (hMax : IsMaximalConsistent S) (f : String)
    (ts : List Term) (pre : List Term) :
    S (.eq (.func f (pre ++ ts.map (fun t => quotientOut (Quotient.mk (termSetoid S hMax) t))))
           (.func f (pre ++ ts))) := by
  induction ts generalizing pre with
  | nil => simp only [List.map_nil, List.append_nil]; exact max_cons_eq_refl hMax _
  | cons t ts' ih =>
    have hEq : S (.eq (quotientOut (Quotient.mk (termSetoid S hMax) t)) t) :=
      Quotient.exact (quotientOut_eq (Quotient.mk (termSetoid S hMax) t))
    have hStep := max_cons_eq_func_step hMax f pre ts'
      (quotientOut (Quotient.mk (termSetoid S hMax) t)) t hEq
    have hIH := ih (pre ++ [quotientOut (Quotient.mk (termSetoid S hMax) t)])
    simp only [List.append_assoc] at hIH
    exact max_cons_eq_trans hMax hIH hStep

mutual
theorem evalTerm_canonical (S : Formula → Prop) (hMax : IsMaximalConsistent S) (t : Term) :
    evalTerm (canonicalModel S hMax) (canonicalEnv S hMax) t =
    Quotient.mk (termSetoid S hMax) t := by
  match t with
  | .bvar n => rfl
  | .fvar x =>
    -- evalTerm canonicalModel canonicalEnv (fvar x) = canonicalFunc x [] = ⟦func x []⟧
    -- We need ⟦func x []⟧ = ⟦fvar x⟧, i.e., S (.eq (func x []) (fvar x)).
    simp only [evalTerm, canonicalModel, canonicalFunc]
    apply Quotient.sound
    have hFvar : S (.eq (.fvar x) (.func x [])) :=
      max_cons_contains hMax ⟨[], fun _ h => (List.not_mem_nil h).elim, fvar_eq_func [] x⟩
    exact max_cons_eq_symm hMax hFvar
  | .func f ts =>
    have ih := evalTerms_canonical S hMax ts
    simp only [evalTerm]
    rw [ih]
    simp only [canonicalModel, canonicalFunc]
    apply Quotient.sound
    simp only [List.map_map, Function.comp_def]
    exact max_cons_eq_func_map hMax f ts []

theorem evalTerms_canonical (S : Formula → Prop) (hMax : IsMaximalConsistent S)
    (ts : List Term) :
    evalTerms (canonicalModel S hMax) (canonicalEnv S hMax) ts =
    ts.map (Quotient.mk (termSetoid S hMax)) := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    simp only [evalTerms, List.map_cons]
    congr 1
    · exact evalTerm_canonical S hMax t
    · exact evalTerms_canonical S hMax ts'
end

-- ============================================================
-- Propiedad de Henkin
-- ============================================================

def IsHenkin (S : Formula → Prop) : Prop :=
  ∀ f, S (.ex f) → ∃ t : Term, S (substFormula 0 t f)

def formulaComplexity : Formula → Nat
  | .bottom | .eq _ _ | .atom _ _ => 0
  | .impl f1 f2 | .and f1 f2 | .or f1 f2 =>
      max (formulaComplexity f1) (formulaComplexity f2) + 1
  | .forall f1 | .ex f1 => formulaComplexity f1 + 1

@[simp]
theorem complexity_substFormula (v : Nat) (t : Term) (f : Formula) :
    formulaComplexity (substFormula v t f) = formulaComplexity f := by
  induction f generalizing v t with
  | bottom | eq _ _ | atom _ _ => rfl
  | impl f1 f2 ih1 ih2 | and f1 f2 ih1 ih2 | or f1 f2 ih1 ih2 =>
      simp [formulaComplexity, substFormula, ih1, ih2]
  | «forall» f1 ih | ex f1 ih => simp [formulaComplexity, substFormula, ih]

theorem max_cons_eq_atom_step {S : Formula → Prop} (hMax : IsMaximalConsistent S) (p : String)
    (pre post : List Term) (t1 t2 : Term) (hEq : S (.eq t1 t2)) :
    S (.atom p (pre ++ t1 :: post)) ↔ S (.atom p (pre ++ t2 :: post)) := by
  let A := Formula.atom p (liftTerms 0 pre ++ .bvar 0 :: liftTerms 0 post)
  have h2 := substTerms_bvar_zero_cons t1 post
  have h4 := substTerms_bvar_zero_cons t2 post
  have hSubst1 : substFormula 0 t1 A = .atom p (pre ++ t1 :: post) := by
    simp only [A, substFormula, substTerms_append, subst_lift_terms_cancel pre t1 0, h2]
  have hSubst2 : substFormula 0 t2 A = .atom p (pre ++ t2 :: post) := by
    simp only [A, substFormula, substTerms_append, subst_lift_terms_cancel pre t2 0, h4]
  constructor
  · intro h1
    exact hSubst2 ▸ max_cons_eq_subst hMax hEq (hSubst1 ▸ h1)
  · intro h2'
    exact hSubst1 ▸ max_cons_eq_subst hMax (max_cons_eq_symm hMax hEq) (hSubst2 ▸ h2')

theorem max_cons_eq_atom_map {S : Formula → Prop} (hMax : IsMaximalConsistent S) (p : String)
    (ts : List Term) (pre : List Term) :
    S (.atom p (pre ++ ts.map (fun t => quotientOut (Quotient.mk (termSetoid S hMax) t)))) ↔
    S (.atom p (pre ++ ts)) := by
  induction ts generalizing pre with
  | nil => simp
  | cons t ts' ih =>
    have hEq : S (.eq (quotientOut (Quotient.mk (termSetoid S hMax) t)) t) :=
      Quotient.exact (quotientOut_eq (Quotient.mk (termSetoid S hMax) t))
    have hStep := max_cons_eq_atom_step hMax p pre ts'
      (quotientOut (Quotient.mk (termSetoid S hMax) t)) t hEq
    have hIH := ih (pre ++ [quotientOut (Quotient.mk (termSetoid S hMax) t)])
    simp only [List.append_assoc] at hIH
    exact Iff.trans hIH hStep

theorem max_cons_ex {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S)
    {A : Formula} : S (.ex A) ↔ ∃ t, S (substFormula 0 t A) := by
  constructor
  · exact hHenkin A
  · intro ⟨t, ht⟩
    apply max_cons_contains hMax
    exact ⟨[substFormula 0 t A],
      fun g hg => by
        cases hg with
        | head _ => exact ht
        | tail _ h => exact (List.not_mem_nil h).elim,
      Derives.intro_ex _ A t (Derives.hyp _ _ (List.Mem.head _))⟩

-- Classical De Morgan for ∀: ¬∀x.A → ∃x.¬A
-- Proof: apply DNE to ∃x.¬A; show ¬¬(∃x.¬A) by assuming ¬∃x.¬A,
-- proving ∀x.A (using DNE pointwise), contradicting ¬∀x.A.
theorem forall_not_impl_exists_not_cl {Γ : List Formula} {A : Formula} :
    Γ ⊢ .impl (neg (.forall A)) (.ex (neg A)) := by
  apply Derives.intro_impl
  apply Derives.elim_impl (A := neg (neg (.ex (neg A))))
  · exact classical_dne _ _
  · apply Derives.intro_impl
    apply Derives.elim_impl (A := .forall A)
    · exact Derives.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
    · apply Derives.intro_forall
      apply Derives.elim_impl (A := neg (neg A))
      · exact classical_dne _ _
      · apply Derives.intro_impl
        apply Derives.elim_impl (A := .ex (neg (liftFormula 1 A)))
        · exact Derives.hyp _ _ (List.Mem.tail _ (List.Mem.head _))
        · apply Derives.intro_ex (t := .bvar 0)
          have hSubst : substFormula 0 (.bvar 0) (neg (liftFormula 1 A)) = neg A := by
            show Formula.impl (substFormula 0 (.bvar 0) (liftFormula 1 A)) ⊥ = Formula.impl A ⊥
            rw [subst_lift_cancel_formula]
          rw [hSubst]
          exact Derives.hyp _ _ (List.Mem.head _)

theorem max_cons_forall {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S)
    {A : Formula} : S (.forall A) ↔ ∀ t, S (substFormula 0 t A) := by
  constructor
  · intro hAll t
    apply max_cons_contains hMax
    exact ⟨[.forall A],
      fun g hg => by
        cases hg with
        | head _ => exact hAll
        | tail _ h => exact (List.not_mem_nil h).elim,
      Derives.elim_forall _ A t (Derives.hyp _ _ (List.Mem.head _))⟩
  · intro hAll
    rcases Classical.em (S (.forall A)) with hForall | hNotAll
    · exact hForall
    · exfalso
      have hInc : (fun x => S x ∨ x = .forall A) ⊢* ⊥ :=
        byContradiction fun hC => hMax.right (.forall A) hNotAll hC
      have hNegForall : S ⊢* neg (.forall A) := DerivesSet_intro_impl' hInc
      -- Classical: ¬∀x.A → ∃x.¬A (requires classical De Morgan in object system)
      have hExNeg_impl : S ⊢* .impl (neg (.forall A)) (.ex (neg A)) :=
        ⟨[], fun _ h => (List.not_mem_nil h).elim, forall_not_impl_exists_not_cl⟩
      have hExNeg := DerivesSet_elim_impl hExNeg_impl hNegForall
      obtain ⟨t, ht⟩ := hHenkin (neg A) (max_cons_contains hMax hExNeg)
      apply hMax.left
      exact ⟨[neg (substFormula 0 t A), substFormula 0 t A],
        fun g hg => by
          cases hg with
          | head _ => exact ht
          | tail _ hT => cases hT with
            | head _ => exact hAll t
            | tail _ h => exact (List.not_mem_nil h).elim,
        Derives.elim_impl _ (substFormula 0 t A) .bottom
          (Derives.hyp _ _ (List.Mem.head _))
          (Derives.hyp _ _ (List.Mem.tail _ (List.Mem.head _)))⟩

-- ============================================================
-- Lema de la Verdad (por recursión en complejidad)
-- ============================================================

theorem truth_lemma {S : Formula → Prop} (hMax : IsMaximalConsistent S) (hHenkin : IsHenkin S)
    (f : Formula) :
    evalFormula (canonicalModel S hMax) (canonicalEnv S hMax) f ↔ S f := by
  cases f with
  | bottom =>
    simp only [evalFormula]
    exact ⟨False.elim, max_cons_bot hMax⟩
  | eq t1 t2 =>
    simp only [evalFormula, evalTerm_canonical S hMax]
    constructor
    · intro h; exact Quotient.exact h
    · intro h; exact Quotient.sound h
  | atom p ts =>
    -- rewrite evalTerms first, then expand model
    have hrw := evalTerms_canonical S hMax ts
    simp only [evalFormula]
    rw [hrw]
    simp only [canonicalModel, canonicalRel, List.map_map, Function.comp_def]
    have hMap := max_cons_eq_atom_map hMax p ts []
    simp only [List.nil_append] at hMap
    exact hMap
  | impl f1 f2 =>
    have ih1 := truth_lemma hMax hHenkin f1
    have ih2 := truth_lemma hMax hHenkin f2
    simp only [evalFormula, ih1, ih2]
    exact (max_cons_impl hMax).symm
  | and f1 f2 =>
    have ih1 := truth_lemma hMax hHenkin f1
    have ih2 := truth_lemma hMax hHenkin f2
    simp only [evalFormula, ih1, ih2]
    exact (max_cons_and hMax).symm
  | or f1 f2 =>
    have ih1 := truth_lemma hMax hHenkin f1
    have ih2 := truth_lemma hMax hHenkin f2
    simp only [evalFormula, ih1, ih2]
    exact (max_cons_or hMax).symm
  | «forall» f1 =>
    simp only [evalFormula]
    constructor
    · intro hall
      apply (max_cons_forall hMax hHenkin).mpr
      intro t
      have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
      rw [evalTerm_canonical S hMax t] at hSubst
      -- hSubst : evalFormula M env (substFormula 0 t f1) ↔ evalFormula M (shiftEnv env (mk t)) f1
      exact (truth_lemma hMax hHenkin (substFormula 0 t f1)).mp (hSubst.mpr (hall _))
    · intro hS d
      obtain ⟨t, ht⟩ := Quotient.exists_rep d; subst ht
      have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
      rw [evalTerm_canonical S hMax t] at hSubst
      exact hSubst.mp ((truth_lemma hMax hHenkin (substFormula 0 t f1)).mpr
              ((max_cons_forall hMax hHenkin).mp hS t))
  | ex f1 =>
    simp only [evalFormula]
    constructor
    · intro ⟨d, hd⟩
      obtain ⟨t, ht⟩ := Quotient.exists_rep d; subst ht
      have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
      rw [evalTerm_canonical S hMax t] at hSubst
      exact (max_cons_ex hMax hHenkin).mpr
              ⟨t, (truth_lemma hMax hHenkin (substFormula 0 t f1)).mp (hSubst.mpr hd)⟩
    · intro hS
      obtain ⟨t, ht⟩ := (max_cons_ex hMax hHenkin).mp hS
      refine ⟨Quotient.mk (termSetoid S hMax) t, ?_⟩
      have hSubst := eval_substFormula_zero (canonicalModel S hMax) (canonicalEnv S hMax) t f1
      rw [evalTerm_canonical S hMax t] at hSubst
      exact hSubst.mp ((truth_lemma hMax hHenkin (substFormula 0 t f1)).mpr ht)
termination_by formulaComplexity f
decreasing_by all_goals simp +arith [formulaComplexity, complexity_substFormula,
    Nat.le_max_left, Nat.le_max_right]

-- ============================================================
-- Extensión de Henkin y Completitud
-- ============================================================

axiom henkin_extension_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    ∃ (S' : Formula → Prop), IsMaximalConsistent S' ∧ IsHenkin S' ∧ (∀ f, S f → S' f)

def IsSatisfiable (S : Formula → Prop) : Prop :=
  ∃ (D : Type) (M : Model D) (v : Nat → D), ∀ f, S f → evalFormula M v f

theorem model_existence_lemma {S : Formula → Prop} (hCons : IsConsistent S) :
    IsSatisfiable S := by
  obtain ⟨S', hMax, hHenkin, hSub⟩ := henkin_extension_lemma hCons
  exact ⟨CanonicalDomain S' hMax, canonicalModel S' hMax, canonicalEnv S' hMax,
         fun f hf => (truth_lemma hMax hHenkin f).mpr (hSub f hf)⟩

theorem completeness {Γ : List Formula} {f : Formula} (h : Γ ⊨ f) : Γ ⊢ f := by
  apply Classical.byContradiction; intro hNotDerive
  have hCons : IsConsistent (fun x => (x ∈ Γ) ∨ (x = neg f)) := by
    intro hBot
    have hImpl : (fun y => y ∈ Γ) ⊢* .impl (neg f) ⊥ := DerivesSet_intro_impl' hBot
    obtain ⟨Γ_sub, hΓ_sub, hDer_impl⟩ := hImpl
    exact hNotDerive (Derives.weakening _ _ _
      (Derives.elim_impl _ (neg (neg f)) f
        (classical_dne Γ_sub f)
        hDer_impl)
      hΓ_sub)
  obtain ⟨D, M, v, hModel⟩ := model_existence_lemma hCons
  exact hModel (neg f) (Or.inr rfl) (h D M v (fun g hg => hModel g (Or.inl hg)))

end FOL.Metamath.Completeness

export FOL.Metamath.Completeness (
  DerivesSet IsConsistent IsMaximalConsistent IsSatisfiable
  model_existence_lemma completeness
)
