import FOL.FOL
import FOL.Tactics.Basic

namespace FOL.Metamath.Semantics

-- ============================================================
-- Fase 5: Semántica y Modelos
-- ============================================================

structure Model (D : Type) where
  func : String → List D → D
  rel  : String → List D → Prop

mutual
def evalTerm {D : Type} (M : Model D) (v : Nat → D) (t : Term) : D :=
  match t with
  | .bvar n => v n
  | .fvar x => M.func x []
  | .func f ts => M.func f (evalTerms M v ts)

def evalTerms {D : Type} (M : Model D) (v : Nat → D) (ts : List Term) : List D :=
  match ts with
  | [] => []
  | t :: ts' => evalTerm M v t :: evalTerms M v ts'
end

def shiftEnv {D : Type} (v : Nat → D) (d : D) : Nat → D
  | 0 => d
  | n + 1 => v n

def updateEnv {D : Type} (c : Nat) (v : Nat → D) (d : D) : Nat → D :=
  fun n =>
    if n < c then v n
    else if n = c then d
    else v (n - 1)

@[simp]
theorem updateEnv_zero {D : Type} (v : Nat → D) (d : D) (n : Nat) :
    updateEnv 0 v d n = shiftEnv v d n := by
  cases n <;> simp [updateEnv, shiftEnv]

theorem updateEnv_zero_eq {D : Type} (v : Nat → D) (d : D) :
    updateEnv 0 v d = shiftEnv v d := by
  funext n
  exact updateEnv_zero v d n

def evalFormula {D : Type} (M : Model D) (v : Nat → D) (f : Formula) : Prop :=
  match f with
  | .bottom => False
  | .eq t1 t2 => evalTerm M v t1 = evalTerm M v t2
  | .atom p ts => M.rel p (evalTerms M v ts)
  | .impl f1 f2 => evalFormula M v f1 → evalFormula M v f2
  | .forall f1 => ∀ (d : D), evalFormula M (shiftEnv v d) f1
  | .and f1 f2 => evalFormula M v f1 ∧ evalFormula M v f2
  | .or f1 f2 => evalFormula M v f1 ∨ evalFormula M v f2
  | .ex f1 => ∃ (d : D), evalFormula M (shiftEnv v d) f1

def contextSatisfies {D : Type} (M : Model D) (v : Nat → D) (Γ : List Formula) : Prop :=
  ∀ f, f ∈ Γ → evalFormula M v f

def satisfies (Γ : List Formula) (f : Formula) : Prop :=
  ∀ (D : Type) (M : Model D) (v : Nat → D), contextSatisfies M v Γ → evalFormula M v f

-- ============================================================
-- Lemas de Sustitución Semántica (Lifting y Sustitución)
-- ============================================================

-- 1. Lemas generalizados para Términos (Profundidad 'c')

mutual
theorem eval_liftTerm_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (t : Term) :
    evalTerm M (updateEnv c v d) (liftTerm c t) = evalTerm M v t := by
  match t with
  | .bvar n =>
    by_cases h : n < c
    · simp [liftTerm, evalTerm, updateEnv, h]
    · have h1 : ¬(n + 1 < c) := by omega
      have h2 : ¬(n + 1 = c) := by omega
      have h3 : n + 1 - 1 = n := by omega
      simp [liftTerm, evalTerm, updateEnv, h, h1, h2, h3]
  | .fvar x => rfl
  | .func f ts =>
    have ih := eval_liftTerms_ext M v d c ts
    simp [liftTerm, evalTerm, ih]

theorem eval_liftTerms_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (ts : List Term) :
    evalTerms M (updateEnv c v d) (liftTerms c ts) = evalTerms M v ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    have ih1 := eval_liftTerm_ext M v d c t
    have ih2 := eval_liftTerms_ext M v d c ts'
    simp [liftTerms, evalTerms, ih1, ih2]
end

mutual
theorem eval_substTerm_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (t : Term) :
    evalTerm M v (substTerm c s t) = evalTerm M (updateEnv c v (evalTerm M v s)) t := by
  match t with
  | .bvar n =>
    by_cases h1 : n = c
    · simp [substTerm, evalTerm, updateEnv, h1]
    · by_cases h3 : n < c
      · have h4 : ¬(n > c) := by omega
        simp [substTerm, evalTerm, updateEnv, h1, h3, h4]
      · have h4 : n > c := by omega
        simp [substTerm, evalTerm, updateEnv, h1, h3, h4]
  | .fvar x => rfl
  | .func f ts =>
    have ih := eval_substTerms_ext M v s c ts
    simp [substTerm, evalTerm, ih]

theorem eval_substTerms_ext {D : Type} (M : Model D) (v : Nat → D) (s : Term) (c : Nat) (ts : List Term) :
    evalTerms M v (substTerms c s ts) = evalTerms M (updateEnv c v (evalTerm M v s)) ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    have ih1 := eval_substTerm_ext M v s c t
    have ih2 := eval_substTerms_ext M v s c ts'
    simp [substTerms, evalTerms, ih1, ih2]
end

-- 2. Lemas generalizados para Fórmulas (Firmas)

theorem shiftEnv_updateEnv_comm {D : Type} (v : Nat → D) (c : Nat) (d d' : D) :
    shiftEnv (updateEnv c v d) d' = updateEnv (c + 1) (shiftEnv v d') d := by
  funext n
  cases n with
  | zero => rfl
  | succ n' =>
    simp only [shiftEnv, updateEnv]
    by_cases h1 : n' < c
    · have h2 : n' + 1 < c + 1 := by omega
      simp [h1, h2]
    · by_cases h2 : n' = c
      · simp [h2]
      · have h3 : ¬(n' + 1 < c + 1) := by omega
        cases n' with
        | zero => omega
        | succ n'' =>
          have h5 : n'' + 1 - 1 = n'' := by omega
          simp [h1, h2, h3, h5]

theorem eval_liftFormula_ext {D : Type} (M : Model D) (v : Nat → D) (d : D) (c : Nat) (f : Formula) :
    evalFormula M (updateEnv c v d) (liftFormula c f) ↔ evalFormula M v f := by
  induction f generalizing c v with
  | bottom => rfl
  | eq t1 t2 =>
    simp only [evalFormula, liftFormula, eval_liftTerm_ext]
  | atom p ts =>
    simp only [evalFormula, liftFormula, eval_liftTerms_ext]
  | impl f1 f2 ih1 ih2 =>
    simp only [evalFormula, liftFormula, ih1, ih2]
  | and f1 f2 ih1 ih2 =>
    simp only [evalFormula, liftFormula, ih1, ih2]
  | or f1 f2 ih1 ih2 =>
    simp only [evalFormula, liftFormula, ih1, ih2]
  | «forall» f1 ih =>
    simp only [evalFormula, liftFormula]
    apply Iff.intro
    · intro h d'
      have h1 := h d'
      rw [shiftEnv_updateEnv_comm] at h1
      exact (ih (shiftEnv v d') (c + 1)).mp h1
    · intro h d'
      have h1 := (ih (shiftEnv v d') (c + 1)).mpr (h d')
      rw [← shiftEnv_updateEnv_comm] at h1
      exact h1
  | ex f1 ih =>
    simp only [evalFormula, liftFormula]
    apply Iff.intro
    · intro ⟨d', hd'⟩
      apply Exists.intro d'
      rw [shiftEnv_updateEnv_comm] at hd'
      exact (ih (shiftEnv v d') (c + 1)).mp hd'
    · intro ⟨d', hd'⟩
      apply Exists.intro d'
      have hd'' := (ih (shiftEnv v d') (c + 1)).mpr hd'
      rw [← shiftEnv_updateEnv_comm] at hd''
      exact hd''

theorem eval_substFormula_ext {D : Type} (M : Model D) (v : Nat → D) (t : Term) (c : Nat) (f : Formula) :
    evalFormula M v (substFormula c t f) ↔ evalFormula M (updateEnv c v (evalTerm M v t)) f := by
  induction f generalizing c v t with
  | bottom => rfl
  | eq t1 t2 =>
    simp only [evalFormula, substFormula, eval_substTerm_ext]
  | atom p ts =>
    simp only [evalFormula, substFormula, eval_substTerms_ext]
  | impl f1 f2 ih1 ih2 =>
    simp only [evalFormula, substFormula, ih1, ih2]
  | and f1 f2 ih1 ih2 =>
    simp only [evalFormula, substFormula, ih1, ih2]
  | or f1 f2 ih1 ih2 =>
    simp only [evalFormula, substFormula, ih1, ih2]
  | «forall» f1 ih =>
    simp only [evalFormula, substFormula]
    apply Iff.intro
    · intro h d'
      have hd' := (ih (shiftEnv v d') (liftTerm 0 t) (c + 1)).mp (h d')
      have hLift : evalTerm M (shiftEnv v d') (liftTerm 0 t) = evalTerm M v t := by
        have h0 := eval_liftTerm_ext M v d' 0 t
        rw [updateEnv_zero_eq] at h0
        exact h0
      rw [hLift, ← shiftEnv_updateEnv_comm] at hd'
      exact hd'
    · intro h d'
      have hd' := h d'
      have hLift : evalTerm M (shiftEnv v d') (liftTerm 0 t) = evalTerm M v t := by
        have h0 := eval_liftTerm_ext M v d' 0 t
        rw [updateEnv_zero_eq] at h0
        exact h0
      rw [shiftEnv_updateEnv_comm, ← hLift] at hd'
      exact (ih (shiftEnv v d') (liftTerm 0 t) (c + 1)).mpr hd'
  | ex f1 ih =>
    simp only [evalFormula, substFormula]
    apply Iff.intro
    · intro ⟨d', h⟩
      apply Exists.intro d'
      have hd' := (ih (shiftEnv v d') (liftTerm 0 t) (c + 1)).mp h
      have hLift : evalTerm M (shiftEnv v d') (liftTerm 0 t) = evalTerm M v t := by
        have h0 := eval_liftTerm_ext M v d' 0 t
        rw [updateEnv_zero_eq] at h0
        exact h0
      rw [hLift, ← shiftEnv_updateEnv_comm] at hd'
      exact hd'
    · intro ⟨d', h⟩
      apply Exists.intro d'
      have hd' := h
      have hLift : evalTerm M (shiftEnv v d') (liftTerm 0 t) = evalTerm M v t := by
        have h0 := eval_liftTerm_ext M v d' 0 t
        rw [updateEnv_zero_eq] at h0
        exact h0
      rw [shiftEnv_updateEnv_comm, ← hLift] at hd'
      exact (ih (shiftEnv v d') (liftTerm 0 t) (c + 1)).mpr hd'

@[simp]
theorem eval_liftFormula_zero {D : Type} (M : Model D) (v : Nat → D) (d : D) (f : Formula) :
    evalFormula M (shiftEnv v d) (liftFormula 0 f) ↔ evalFormula M v f := by
  have h := eval_liftFormula_ext M v d 0 f
  rw [updateEnv_zero_eq] at h
  exact h

@[simp]
theorem eval_substFormula_zero {D : Type} (M : Model D) (v : Nat → D) (t : Term) (f : Formula) :
    evalFormula M v (substFormula 0 t f) ↔ evalFormula M (shiftEnv v (evalTerm M v t)) f := by
  have h := eval_substFormula_ext M v t 0 f
  rw [updateEnv_zero_eq] at h
  exact h

theorem contextSatisfies_lift_zero {D : Type} (M : Model D) (v : Nat → D) (d : D) {Γ : List Formula} :
    contextSatisfies M (shiftEnv v d) (Γ.map (liftFormula 0)) ↔ contextSatisfies M v Γ := by
  unfold contextSatisfies
  apply Iff.intro
  · intro h f hIn
    have hMap : liftFormula 0 f ∈ Γ.map (liftFormula 0) := by
      rw [List.mem_map]
      exact ⟨f, hIn, rfl⟩
    exact (eval_liftFormula_zero M v d f).mp (h _ hMap)
  · intro h f' hIn
    rw [List.mem_map] at hIn
    obtain ⟨f, hIn_f, rfl⟩ := hIn
    exact (eval_liftFormula_zero M v d f).mpr (h f hIn_f)

-- ============================================================
-- Lemas de Corrección de Reescritura Local
-- ============================================================

theorem rule_soundness {D : Type} (M : Model D) (v : Nat → D) {A B : Formula} (h : LocalRule A B) :
    evalFormula M v A ↔ evalFormula M v B := by
  cases h
  simp only [evalFormula]
  apply Iff.intro
  · intro h1 h2 h3; exact h1 h3 h2
  · intro h1 h2 h3; exact h1 h3 h2

theorem replaceAt_soundness {D : Type} (M : Model D) (v : Nat → D) {f sub sub' : Formula} {p : Pos}
    (hGet : getAt? f p = some sub) (hEq : ∀ v', evalFormula M v' sub ↔ evalFormula M v' sub') :
    evalFormula M v f ↔ evalFormula M v (replaceAt f p sub') := by
  induction p generalizing f v with
  | root =>
    simp only [getAt?] at hGet
    injection hGet with heq
    subst heq
    simp only [replaceAt]
    exact hEq v
  | left p' ih =>
    cases f with
    | impl f1 f2 =>
      have ih' := ih v (by simp [getAt?] at hGet; exact hGet)
      have _type_check : evalFormula M v f1 ↔ evalFormula M v (replaceAt f1 p' sub') := ih'
      simp only [replaceAt, evalFormula]
      apply Iff.intro
      · intro h1 h2
        have h3 : evalFormula M v f1 := ih'.mpr h2
        exact h1 h3
      · intro h1 h2
        have h3 : evalFormula M v (replaceAt f1 p' sub') := ih'.mp h2
        exact h1 h3
    | and f1 f2 =>
      have hGet' : getAt? f1 p' = some sub := by simp [getAt?] at hGet; exact hGet
      have ih' := ih v hGet'
      have _type_check : evalFormula M v f1 ↔ evalFormula M v (replaceAt f1 p' sub') := ih'
      simp only [replaceAt, evalFormula]
      apply Iff.intro
      · intro ⟨h1, h2⟩
        have h3 : evalFormula M v (replaceAt f1 p' sub') := ih'.mp h1
        exact ⟨h3, h2⟩
      · intro ⟨h1, h2⟩
        have h3 : evalFormula M v f1 := ih'.mpr h1
        exact ⟨h3, h2⟩
    | or f1 f2 =>
      have hGet' : getAt? f1 p' = some sub := by simp [getAt?] at hGet; exact hGet
      have ih' := ih v hGet'
      have _type_check : evalFormula M v f1 ↔ evalFormula M v (replaceAt f1 p' sub') := ih'
      simp only [replaceAt, evalFormula]
      apply Iff.intro
      · intro h
        cases h with
        | inl h1 =>
          have h3 : evalFormula M v (replaceAt f1 p' sub') := ih'.mp h1
          exact Or.inl h3
        | inr h2 => exact Or.inr h2
      · intro h
        cases h with
        | inl h1 =>
          have h3 : evalFormula M v f1 := ih'.mpr h1
          exact Or.inl h3
        | inr h2 => exact Or.inr h2
    | _ =>
      simp only [getAt?] at hGet
      contradiction
  | right p' ih =>
    cases f with
    | impl f1 f2 =>
      have hGet' : getAt? f2 p' = some sub := by simp [getAt?] at hGet; exact hGet
      have ih' := ih v hGet'
      simp only [replaceAt, evalFormula]
      apply Iff.intro
      · intro h1 h2
        have h3 : evalFormula M v f2 := h1 h2
        have h4 : evalFormula M v (replaceAt f2 p' sub') := ih'.mp h3
        exact h4
      · intro h1 h2
        have h3 : evalFormula M v (replaceAt f2 p' sub') := h1 h2
        have h4 : evalFormula M v f2 := ih'.mpr h3
        exact h4
    | and f1 f2 =>
      have hGet' : getAt? f2 p' = some sub := by simp [getAt?] at hGet; exact hGet
      have ih' := ih v hGet'
      simp only [replaceAt, evalFormula]
      apply Iff.intro
      · intro ⟨h1, h2⟩
        have h3 : evalFormula M v f2 := h2
        have h4 : evalFormula M v (replaceAt f2 p' sub') := ih'.mp h3
        exact ⟨h1, h4⟩
      · intro ⟨h1, h2⟩
        have h3 : evalFormula M v (replaceAt f2 p' sub') := h2
        have h4 : evalFormula M v f2 := ih'.mpr h3
        exact ⟨h1, h4⟩
    | or f1 f2 =>
      have hGet' : getAt? f2 p' = some sub := by simp [getAt?] at hGet; exact hGet
      have ih' := ih v hGet'
      simp only [replaceAt, evalFormula]
      apply Iff.intro
      · intro h
        cases h with
        | inl h1 => exact Or.inl h1
        | inr h2 =>
          have h3 : evalFormula M v f2 := h2
          have h4 : evalFormula M v (replaceAt f2 p' sub') := ih'.mp h3
          exact Or.inr h4
      · intro h
        cases h with
        | inl h1 => exact Or.inl h1
        | inr h2 =>
          have h3 : evalFormula M v (replaceAt f2 p' sub') := h2
          have h4 : evalFormula M v f2 := ih'.mpr h3
          exact Or.inr h4
    | _ =>
      simp only [getAt?] at hGet
      contradiction
  | body p' ih =>
    cases f with
    | «forall» f1 =>
      simp only [getAt?, replaceAt, evalFormula] at hGet ⊢
      apply Iff.intro
      · intro h d; exact (ih (shiftEnv v d) hGet).mp (h d)
      · intro h d; exact (ih (shiftEnv v d) hGet).mpr (h d)
    | ex f1 =>
      simp only [getAt?, replaceAt, evalFormula] at hGet ⊢
      apply Iff.intro
      · intro ⟨d, hd⟩; apply Exists.intro d; exact (ih (shiftEnv v d) hGet).mp hd
      · intro ⟨d, hd⟩; apply Exists.intro d; exact (ih (shiftEnv v d) hGet).mpr hd
    | _ =>
      simp only [getAt?] at hGet
      contradiction

end FOL.Metamath.Semantics