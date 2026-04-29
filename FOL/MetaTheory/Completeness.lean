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
import FOL.Util.Encoding

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

-- formula_enum and formula_enum_surj are proved in FOL.Util.Encoding
-- (injective encoding Formula → Nat + Classical.choose)
open FOL.Util.Encoding (formula_enum formula_enum_surj)

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
-- Infraestructura para la extensión de Henkin
-- ============================================================

-- PARTE 1: Sustitución de variables libres (fvar) en términos y fórmulas

private mutual
def fvarSubstTerm (c : String) (s : Term) : Term → Term
  | .bvar n     => .bvar n
  | .fvar x     => if x = c then s else .fvar x
  | .func f ts  => .func f (fvarSubstTerms c s ts)

def fvarSubstTerms (c : String) (s : Term) : List Term → List Term
  | []       => []
  | t :: ts  => fvarSubstTerm c s t :: fvarSubstTerms c s ts
end

private def fvarSubstFormula (c : String) (s : Term) : Formula → Formula
  | .bottom       => .bottom
  | .eq t1 t2     => .eq (fvarSubstTerm c s t1) (fvarSubstTerm c s t2)
  | .atom p ts    => .atom p (fvarSubstTerms c s ts)
  | .impl f1 f2   => .impl (fvarSubstFormula c s f1) (fvarSubstFormula c s f2)
  | .and f1 f2    => .and (fvarSubstFormula c s f1) (fvarSubstFormula c s f2)
  | .or f1 f2     => .or (fvarSubstFormula c s f1) (fvarSubstFormula c s f2)
  | .forall f1    => .forall (fvarSubstFormula c (liftTerm 0 s) f1)
  | .ex f1        => .ex (fvarSubstFormula c (liftTerm 0 s) f1)

-- Predicado de frescura: fvar c no aparece en el término/fórmula
private mutual
def fvarFreeTerm (c : String) : Term → Bool
  | .bvar _    => true
  | .fvar x    => !decide (x = c)
  | .func _ ts => fvarFreeTerms c ts

def fvarFreeTerms (c : String) : List Term → Bool
  | []       => true
  | t :: ts  => fvarFreeTerm c t && fvarFreeTerms c ts
end

private def fvarFreeFormula (c : String) : Formula → Bool
  | .bottom       => true
  | .eq t1 t2     => fvarFreeTerm c t1 && fvarFreeTerm c t2
  | .atom _ ts    => fvarFreeTerms c ts
  | .impl f1 f2   | .and f1 f2   | .or f1 f2 =>
      fvarFreeFormula c f1 && fvarFreeFormula c f2
  | .forall f1    | .ex f1       => fvarFreeFormula c f1

-- fvarSubst es la identidad cuando c es fresco
private mutual
theorem fvarSubst_id_term (c : String) (s : Term) (t : Term)
    (h : fvarFreeTerm c t = true) : fvarSubstTerm c s t = t := by
  match t with
  | .bvar _ => rfl
  | .fvar x =>
    simp only [fvarFreeTerm, Bool.not_eq_true', decide_eq_false_iff_not] at h
    simp [fvarSubstTerm, h]
  | .func f ts =>
    simp only [fvarSubstTerm]
    congr 1
    exact fvarSubst_id_terms c s ts h

theorem fvarSubst_id_terms (c : String) (s : Term) (ts : List Term)
    (h : fvarFreeTerms c ts = true) : fvarSubstTerms c s ts = ts := by
  match ts with
  | []       => rfl
  | t :: ts' =>
    simp only [fvarFreeTerms, Bool.and_eq_true] at h
    simp only [fvarSubstTerms]
    exact ⟨fvarSubst_id_term c s t h.1, fvarSubst_id_terms c s ts' h.2⟩ |>.elim
      (fun ht hts => by rw [ht, hts])
end

private theorem fvarSubst_id_formula (c : String) (s : Term) (f : Formula)
    (h : fvarFreeFormula c f = true) : fvarSubstFormula c s f = f := by
  induction f generalizing s with
  | bottom => rfl
  | eq t1 t2 =>
    simp only [fvarFreeFormula, Bool.and_eq_true] at h
    simp [fvarSubstFormula, fvarSubst_id_term c s t1 h.1, fvarSubst_id_term c s t2 h.2]
  | atom _ ts =>
    simp [fvarSubstFormula, fvarSubst_id_terms c s ts h]
  | impl f1 f2 ih1 ih2 | and f1 f2 ih1 ih2 | or f1 f2 ih1 ih2 =>
    simp only [fvarFreeFormula, Bool.and_eq_true] at h
    simp [fvarSubstFormula, ih1 s h.1, ih2 s h.2]
  | «forall» f1 ih | ex f1 ih =>
    simp only [fvarFreeFormula] at h
    simp [fvarSubstFormula, ih (liftTerm 0 s) h]

-- PARTE 2: Conmutatividad de liftTerm y liftFormula

private mutual
theorem liftTerm_comm (b a : Nat) (h : b ≤ a) (t : Term) :
    liftTerm (a + 1) (liftTerm b t) = liftTerm b (liftTerm a t) := by
  match t with
  | .bvar n =>
    simp only [liftTerm]
    split_ifs with h1 h2 h3 h4 h5 <;> try omega <;> try rfl
  | .fvar _ => rfl
  | .func f ts =>
    simp only [liftTerm]
    exact congrArg (Term.func f) (liftTerms_comm b a h ts)

theorem liftTerms_comm (b a : Nat) (h : b ≤ a) (ts : List Term) :
    liftTerms (a + 1) (liftTerms b ts) = liftTerms b (liftTerms a ts) := by
  match ts with
  | []       => rfl
  | t :: ts' =>
    simp only [liftTerms]
    exact ⟨liftTerm_comm b a h t, liftTerms_comm b a h ts'⟩ |>.elim
      (fun ht hts => by rw [ht, hts])
end

private theorem liftFormula_comm (b a : Nat) (h : b ≤ a) (f : Formula) :
    liftFormula (a + 1) (liftFormula b f) = liftFormula b (liftFormula a f) := by
  induction f generalizing b a with
  | bottom => rfl
  | eq t1 t2 =>
    simp [liftFormula, liftTerm_comm b a h t1, liftTerm_comm b a h t2]
  | atom _ ts =>
    simp [liftFormula, liftTerms_comm b a h ts]
  | impl f1 f2 ih1 ih2 | and f1 f2 ih1 ih2 | or f1 f2 ih1 ih2 =>
    simp [liftFormula, ih1 b a h, ih2 b a h]
  | «forall» f1 ih | ex f1 ih =>
    simp [liftFormula, ih (b + 1) (a + 1) (Nat.add_le_add_right h 1)]

-- Conmutatividad especial: 0 ≤ c → liftFormula (c+1) ∘ liftFormula 0 = liftFormula 0 ∘ liftFormula c
private theorem liftFormula_comm_zero (c : Nat) (f : Formula) :
    liftFormula (c + 1) (liftFormula 0 f) = liftFormula 0 (liftFormula c f) :=
  liftFormula_comm 0 c (Nat.zero_le c) f

-- PARTE 3: Conmutatividad de lift y sustitución

private mutual
theorem lift_subst_comm_term (v c : Nat) (h : v ≤ c) (s : Term) (t : Term) :
    liftTerm c (substTerm v s t) = substTerm v (liftTerm c s) (liftTerm (c + 1) t) := by
  match t with
  | .bvar n =>
    simp only [substTerm, liftTerm]
    split_ifs with h1 h2 h3 h4 h5 <;> try omega <;> try rfl
    · omega
  | .fvar _ => simp [substTerm, liftTerm]
  | .func f ts =>
    simp only [substTerm, liftTerm]
    exact congrArg (Term.func f) (lift_subst_comm_terms v c h s ts)

theorem lift_subst_comm_terms (v c : Nat) (h : v ≤ c) (s : Term) (ts : List Term) :
    liftTerms c (substTerms v s ts) = substTerms v (liftTerm c s) (liftTerms (c + 1) ts) := by
  match ts with
  | []       => rfl
  | t :: ts' =>
    simp only [substTerms, liftTerms]
    exact ⟨lift_subst_comm_term v c h s t, lift_subst_comm_terms v c h s ts'⟩ |>.elim
      (fun ht hts => by rw [ht, hts])
end

private theorem lift_subst_comm_formula (v c : Nat) (h : v ≤ c) (s : Term) (f : Formula) :
    liftFormula c (substFormula v s f) =
    substFormula v (liftTerm c s) (liftFormula (c + 1) f) := by
  induction f generalizing v c s with
  | bottom => rfl
  | eq t1 t2 =>
    simp [liftFormula, substFormula, lift_subst_comm_term v c h s t1,
          lift_subst_comm_term v c h s t2]
  | atom _ ts =>
    simp [liftFormula, substFormula, lift_subst_comm_terms v c h s ts]
  | impl f1 f2 ih1 ih2 | and f1 f2 ih1 ih2 | or f1 f2 ih1 ih2 =>
    simp [liftFormula, substFormula, ih1 v c h s, ih2 v c h s]
  | «forall» f1 ih | ex f1 ih =>
    simp only [liftFormula, substFormula]
    have hcomm : liftTerm (c + 1) (liftTerm 0 s) = liftTerm 0 (liftTerm c s) :=
      liftTerm_comm 0 c (Nat.zero_le c) s
    rw [← hcomm]
    exact congrArg Formula.forall (ih (v + 1) (c + 1) (Nat.add_le_add_right h 1) (liftTerm 0 s))

-- Caso especial: v=0, c=0, s=fvar name (que usaremos en la prueba principal)
private theorem lift_subst_comm_zero (s : Term) (A : Formula) :
    liftFormula 0 (substFormula 0 s A) = substFormula 0 (liftTerm 0 s) (liftFormula 1 A) :=
  lift_subst_comm_formula 0 0 (Nat.le_refl 0) s A

-- PARTE 4: Posición y conmutatividad de lift con getAt?/replaceAt

private def posDepth : Pos → Nat
  | .root     => 0
  | .left p   => posDepth p
  | .right p  => posDepth p
  | .body p   => posDepth p + 1

private theorem lift_getAt? (c : Nat) {f : Formula} {p : Pos} {sub : Formula}
    (h : getAt? f p = some sub) :
    getAt? (liftFormula c f) p = some (liftFormula (c + posDepth p) sub) := by
  induction p generalizing f c with
  | root =>
    simp only [getAt?] at h
    simp [getAt?, posDepth, h]
  | left p' ih =>
    simp only [posDepth]
    match f with
    | .impl f1 f2 =>
      simp only [getAt?] at h
      simp [getAt?, liftFormula, ih h]
    | .and f1 f2 =>
      simp only [getAt?] at h
      simp [getAt?, liftFormula, ih h]
    | .or f1 f2 =>
      simp only [getAt?] at h
      simp [getAt?, liftFormula, ih h]
    | _ => simp [getAt?] at h
  | right p' ih =>
    simp only [posDepth]
    match f with
    | .impl f1 f2 =>
      simp only [getAt?] at h
      simp [getAt?, liftFormula, ih h]
    | .and f1 f2 =>
      simp only [getAt?] at h
      simp [getAt?, liftFormula, ih h]
    | .or f1 f2 =>
      simp only [getAt?] at h
      simp [getAt?, liftFormula, ih h]
    | _ => simp [getAt?] at h
  | body p' ih =>
    simp only [posDepth]
    match f with
    | .forall f1 =>
      simp only [getAt?] at h
      simp only [liftFormula, getAt?]
      have := ih (c := c + 1) h
      simp only [posDepth] at this
      convert this using 2
      omega
    | .ex f1 =>
      simp only [getAt?] at h
      simp only [liftFormula, getAt?]
      have := ih (c := c + 1) h
      simp only [posDepth] at this
      convert this using 2
      omega
    | _ => simp [getAt?] at h

private theorem lift_replaceAt (c : Nat) (f : Formula) (p : Pos) (sub' : Formula) :
    liftFormula c (replaceAt f p sub') =
    replaceAt (liftFormula c f) p (liftFormula (c + posDepth p) sub') := by
  induction p generalizing f c with
  | root => simp [replaceAt, posDepth]
  | left p' ih =>
    simp only [posDepth]
    match f with
    | .impl f1 f2 => simp [replaceAt, liftFormula, ih f1]
    | .and f1 f2  => simp [replaceAt, liftFormula, ih f1]
    | .or f1 f2   => simp [replaceAt, liftFormula, ih f1]
    | _ => simp [replaceAt, liftFormula]
  | right p' ih =>
    simp only [posDepth]
    match f with
    | .impl f1 f2 => simp [replaceAt, liftFormula, ih f2]
    | .and f1 f2  => simp [replaceAt, liftFormula, ih f2]
    | .or f1 f2   => simp [replaceAt, liftFormula, ih f2]
    | _ => simp [replaceAt, liftFormula]
  | body p' ih =>
    simp only [posDepth]
    match f with
    | .forall f1 =>
      simp only [replaceAt, liftFormula]
      have h := ih (c := c + 1) f1
      simp only [posDepth] at h
      convert congrArg Formula.forall h using 2
      omega
    | .ex f1 =>
      simp only [replaceAt, liftFormula]
      have h := ih (c := c + 1) f1
      simp only [posDepth] at h
      convert congrArg Formula.ex h using 2
      omega
    | _ => simp [replaceAt, liftFormula]

private theorem lift_LocalRule (d : Nat) {sub sub' : Formula}
    (h : LocalRule sub sub') : LocalRule (liftFormula d sub) (liftFormula d sub') := by
  cases h with
  | commuteImpl A B C =>
    simp only [liftFormula]
    exact LocalRule.commuteImpl (liftFormula d A) (liftFormula d B) (liftFormula d C)

-- PARTE 5: lift_derives_gen — levantar derivaciones

private theorem lift_derives_gen {Γ : List Formula} {f : Formula} (h : Γ ⊢ f) :
    ∀ c, Γ.map (liftFormula c) ⊢ liftFormula c f := by
  intro c
  induction h generalizing c with
  | hyp Γ f hf =>
    exact Derives.hyp _ _ (List.mem_map.mpr ⟨f, hf, rfl⟩)
  | intro_impl Γ A B _ ih =>
    simp only [liftFormula]
    exact Derives.intro_impl _ _ _ (ih c)
  | elim_impl Γ A B _ _ ih1 ih2 =>
    exact Derives.elim_impl _ _ _ (ih1 c) (ih2 c)
  | intro_and Γ A B _ _ ih1 ih2 =>
    simp only [liftFormula]
    exact Derives.intro_and _ _ _ (ih1 c) (ih2 c)
  | elim_and_l Γ A B _ ih =>
    exact Derives.elim_and_l _ _ _ (ih c)
  | elim_and_r Γ A B _ ih =>
    exact Derives.elim_and_r _ _ _ (ih c)
  | intro_or_l Γ A B _ ih =>
    simp only [liftFormula]
    exact Derives.intro_or_l _ _ _ (ih c)
  | intro_or_r Γ A B _ ih =>
    simp only [liftFormula]
    exact Derives.intro_or_r _ _ _ (ih c)
  | elim_or Γ A B C _ _ _ ih1 ih2 ih3 =>
    exact Derives.elim_or _ _ _ _ (ih1 c) (ih2 c) (ih3 c)
  | intro_forall Γ A _ ih =>
    simp only [liftFormula]
    apply Derives.intro_forall
    -- Need: (Γ.map (liftFormula c)).map (liftFormula 0) ⊢ liftFormula (c+1) A
    -- From ih (c+1): (Γ.map (liftFormula 0)).map (liftFormula (c+1)) ⊢ liftFormula (c+1) A
    -- And: (Γ.map (liftFormula 0)).map (liftFormula (c+1)) = (Γ.map (liftFormula c)).map (liftFormula 0)
    have hih := ih (c + 1)
    simp only [List.map_map] at hih ⊢
    convert hih using 2
    ext f
    exact (liftFormula_comm_zero c f).symm
  | elim_forall Γ A t _ ih =>
    simp only [liftFormula]
    rw [lift_subst_comm_formula 0 c (Nat.zero_le c) t A]
    exact Derives.elim_forall _ _ _ (ih c)
  | intro_ex Γ A t _ ih =>
    simp only [liftFormula]
    rw [lift_subst_comm_formula 0 c (Nat.zero_le c) t A]
    exact Derives.intro_ex _ _ _ (ih c)
  | elim_ex Γ A B _ _ ih1 ih2 =>
    simp only [liftFormula]
    apply Derives.elim_ex _ (liftFormula (c + 1) A)
    · exact ih1 c
    · -- Need: liftFormula (c+1) A :: (Γ.map (liftFormula c)).map (liftFormula 0) ⊢ liftFormula 0 (liftFormula c B)
      -- From ih2 (c+1): (A :: Γ.map (liftFormula 0)).map (liftFormula (c+1)) ⊢ liftFormula (c+1) (liftFormula 0 B)
      have hih := ih2 (c + 1)
      simp only [List.map_cons, List.map_map] at hih
      rw [liftFormula_comm 0 c (Nat.zero_le c)] at hih
      convert hih using 1
      · congr 1
        simp only [List.map_map]
        congr 1
        ext f
        exact (liftFormula_comm_zero c f).symm
      · exact (liftFormula_comm 0 c (Nat.zero_le c) B).symm
  | bot_elim Γ A _ ih =>
    exact Derives.bot_elim _ _ (ih c)
  | eq_refl Γ t =>
    simp only [liftFormula]
    exact Derives.eq_refl _ _
  | eq_subst Γ A t1 t2 _ _ ih1 ih2 =>
    simp only [liftFormula]
    rw [lift_subst_comm_formula 0 c (Nat.zero_le c) t1 A,
        lift_subst_comm_formula 0 c (Nat.zero_le c) t2 A]
    exact Derives.eq_subst _ _ _ _ (ih1 c) (ih2 c)
  | weakening Γ Γ' f _ hSub ih =>
    exact Derives.weakening _ _ _ (ih c) (fun x hx =>
      List.mem_map.mpr (let ⟨y, hyΓ', hyeq⟩ := List.mem_map.mp hx
                        ⟨y, hSub y (by simpa using hyΓ'), hyeq⟩))
  | rewrite_at Γ f f' p sub sub' _ hGet hRule hReplace ih =>
    have hGetLift := lift_getAt? c hGet
    have hRuleLift := lift_LocalRule (c + posDepth p) hRule
    have hReplaceLift := (lift_replaceAt c f p sub').symm
    rw [hReplace] at hReplaceLift ⊢
    exact Derives.rewrite_at _ _ _ p _ _
      (ih c) hGetLift hRuleLift (by rw [← lift_replaceAt])

-- PARTE 6: Álgebra de fvarSubst

-- Conmutatividad: fvarSubst y liftTerm
private theorem fvarSubst_liftTerm (c : String) (s : Term) (t : Term) :
    fvarSubstTerm c s (liftTerm 0 t) = liftTerm 0 (fvarSubstTerm c s t) := by
  match t with
  | .bvar n =>
    simp [liftTerm, fvarSubstTerm]
    split_ifs <;> simp [liftTerm]
  | .fvar x => simp [liftTerm, fvarSubstTerm]
  | .func f ts =>
    simp only [liftTerm, fvarSubstTerm]
    congr 1
    induction ts with
    | nil => rfl
    | cons t ts' ih =>
      simp only [liftTerms, fvarSubstTerms]
      rw [fvarSubst_liftTerm c s t, ih]

-- Identidad clave: fvarSubst c (bvar 0) (substFormula 0 (fvar c) (liftFormula 1 A)) = A
-- cuando c ∉ fvars(A)
-- Paso 1: fvarSubst c s (substFormula 0 (fvar c) t) = substTerm 0 s t cuando c ∉ fvars(t)
private mutual
theorem fvarSubst_subst_term (c : String) (s : Term) (t : Term)
    (hfree : fvarFreeTerm c t = true) :
    fvarSubstTerm c s (substTerm 0 (Term.fvar c) t) = substTerm 0 s t := by
  match t with
  | .bvar n =>
    simp only [substTerm]
    split_ifs with h
    · simp [fvarSubstTerm]
    · simp only [fvarSubstTerm]
    · simp only [fvarSubstTerm]
  | .fvar x =>
    simp only [fvarFreeTerm, Bool.not_eq_true', decide_eq_false_iff_not] at hfree
    simp only [substTerm, fvarSubstTerm]
    split_ifs with h
    · exact absurd h hfree
    · simp [fvarSubstTerm, h]
  | .func f ts =>
    simp only [substTerm, fvarSubstTerm]
    exact congrArg (Term.func f) (fvarSubst_subst_terms c s ts hfree)

theorem fvarSubst_subst_terms (c : String) (s : Term) (ts : List Term)
    (hfree : fvarFreeTerms c ts = true) :
    fvarSubstTerms c s (substTerms 0 (Term.fvar c) ts) = substTerms 0 s ts := by
  match ts with
  | []       => rfl
  | t :: ts' =>
    simp only [fvarFreeTerms, Bool.and_eq_true] at hfree
    simp only [substTerms, fvarSubstTerms,
               fvarSubst_subst_term c s t hfree.1,
               fvarSubst_subst_terms c s ts' hfree.2]
end

-- liftTermN: apply liftTerm 0 n times (needed before fvarSubst_subst_formula_gen)
private def liftTermN : Nat → Term → Term
  | 0,     t => t
  | n + 1, t => liftTerm 0 (liftTermN n t)

-- General term/list-level identity: fvarSubst c (liftTermN v s) (substTerm v (fvar c) t) = substTerm v (liftTermN v s) t
-- when fvar c ∉ t  (arbitrary depth v)
private mutual
theorem fvarSubst_subst_term_gen (c : String) (s : Term) (v : Nat) (t : Term)
    (hfree : fvarFreeTerm c t = true) :
    fvarSubstTerm c (liftTermN v s) (substTerm v (Term.fvar c) t) =
    substTerm v (liftTermN v s) t := by
  match t with
  | .bvar n =>
    simp only [substTerm]
    split_ifs with h1 h2
    · -- n = v → substTerm gives fvar c → fvarSubst replaces with liftTermN v s
      simp [fvarSubstTerm]
    · -- n > v → bvar (n-1) → unchanged by fvarSubst
      simp [fvarSubstTerm]
    · -- n < v → bvar n → unchanged by fvarSubst
      simp [fvarSubstTerm]
  | .fvar x =>
    simp only [fvarFreeTerm, Bool.not_eq_true', decide_eq_false_iff_not] at hfree
    simp only [substTerm, fvarSubstTerm]
    split_ifs with h
    · exact absurd h hfree
    · simp [fvarSubstTerm, h]
  | .func f ts =>
    simp only [substTerm, fvarSubstTerm]
    exact congrArg (Term.func f) (fvarSubst_subst_terms_gen c s v ts hfree)

theorem fvarSubst_subst_terms_gen (c : String) (s : Term) (v : Nat) (ts : List Term)
    (hfree : fvarFreeTerms c ts = true) :
    fvarSubstTerms c (liftTermN v s) (substTerms v (Term.fvar c) ts) =
    substTerms v (liftTermN v s) ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    simp only [fvarFreeTerms, Bool.and_eq_true] at hfree
    simp only [substTerms, fvarSubstTerms,
               fvarSubst_subst_term_gen c s v t hfree.1,
               fvarSubst_subst_terms_gen c s v ts' hfree.2]
end

-- General formula-level identity at arbitrary depth v
private theorem fvarSubst_subst_formula_gen (c : String) (s : Term) (v : Nat) (f : Formula)
    (hfree : fvarFreeFormula c f = true) :
    fvarSubstFormula c (liftTermN v s) (substFormula v (Term.fvar c) f) =
    substFormula v (liftTermN v s) f := by
  induction f generalizing v with
  | bottom => rfl
  | eq t1 t2 =>
    simp only [fvarFreeFormula, Bool.and_eq_true] at hfree
    simp [substFormula, fvarSubstFormula,
          fvarSubst_subst_term_gen c s v t1 hfree.1,
          fvarSubst_subst_term_gen c s v t2 hfree.2]
  | atom _ ts =>
    simp [substFormula, fvarSubstFormula, fvarSubst_subst_terms_gen c s v ts hfree]
  | impl f1 f2 ih1 ih2 | and f1 f2 ih1 ih2 | or f1 f2 ih1 ih2 =>
    simp only [fvarFreeFormula, Bool.and_eq_true] at hfree
    simp [substFormula, fvarSubstFormula, ih1 v hfree.1, ih2 v hfree.2]
  | «forall» f1 ih =>
    simp only [fvarFreeFormula] at hfree
    -- By definition: both sides reduce to forall (...) with v+1
    -- liftTerm 0 (fvar c) = fvar c and liftTerm 0 (liftTermN v s) = liftTermN (v+1) s (definitional)
    show Formula.forall (fvarSubstFormula c (liftTermN (v + 1) s)
           (substFormula (v + 1) (Term.fvar c) f1)) =
         Formula.forall (substFormula (v + 1) (liftTermN (v + 1) s) f1)
    exact congrArg Formula.forall (ih (v + 1) hfree)
  | ex f1 ih =>
    simp only [fvarFreeFormula] at hfree
    show Formula.ex (fvarSubstFormula c (liftTermN (v + 1) s)
           (substFormula (v + 1) (Term.fvar c) f1)) =
         Formula.ex (substFormula (v + 1) (liftTermN (v + 1) s) f1)
    exact congrArg Formula.ex (ih (v + 1) hfree)

-- Corollary at depth 0: fvarSubst c s (substFormula 0 (fvar c) f) = substFormula 0 s f
private theorem fvarSubst_subst_formula (c : String) (s : Term) (f : Formula)
    (hfree : fvarFreeFormula c f = true) :
    fvarSubstFormula c s (substFormula 0 (Term.fvar c) f) = substFormula 0 s f :=
  fvarSubst_subst_formula_gen c s 0 f hfree

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
