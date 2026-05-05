/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

/-
  Encoding of Formula into Nat, used to prove countability of Formula
  and to define formula_enum / formula_enum_surj without axioms.

  NOTE: FOL.FOL defines `infixr:70 " ∧ " => Formula.and`, which shadows
  the built-in Prop-level ∧. To avoid ambiguity, we use `And` explicitly
  for all proposition conjunctions in this file.
-/

import FOL.FOL

namespace FOL.Util.Encoding

-- ============================================================
-- npair: injective pairing function
-- npair 0 b   = 2*b        (always even)
-- npair (a+1) b = 2*(npair a b) + 1  (always odd)
-- ============================================================

def npair : Nat → Nat → Nat
  | 0, b => 2 * b
  | a + 1, b => 2 * npair a b + 1

-- Return type uses And explicitly (not ∧, which is Formula.and in this project).
theorem npair_inj {a b c d : Nat} (h : npair a b = npair c d) : And (a = c) (b = d) := by
  induction a generalizing b c d with
  | zero =>
    cases c with
    | zero =>
      simp only [npair] at h
      exact ⟨rfl, by omega⟩
    | succ c' =>
      simp only [npair] at h
      omega
  | succ a ih =>
    cases c with
    | zero =>
      simp only [npair] at h
      omega
    | succ c' =>
      simp only [npair] at h
      have heq : npair a b = npair c' d := by omega
      obtain ⟨ha, hb⟩ := ih heq
      exact ⟨by omega, hb⟩

-- ============================================================
-- List Nat encoding
-- [] ↦ 0, (n :: ns) ↦ npair n (encodeList ns) + 1
-- ============================================================

def encodeList : List Nat → Nat
  | [] => 0
  | n :: ns => npair n (encodeList ns) + 1

theorem encodeList_inj {xs ys : List Nat} (h : encodeList xs = encodeList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys' =>
      simp only [encodeList] at h
      omega
  | cons x xs' ih =>
    cases ys with
    | nil =>
      simp only [encodeList] at h
      omega
    | cons y ys' =>
      simp only [encodeList] at h
      have heq : npair x (encodeList xs') = npair y (encodeList ys') := by omega
      obtain ⟨hx, hxs⟩ := npair_inj heq
      rw [hx, ih hxs]

-- ============================================================
-- Char / String encoding
-- ============================================================

def encodeChar (c : Char) : Nat := c.val.toNat

theorem encodeChar_inj {c d : Char} (h : encodeChar c = encodeChar d) : c = d :=
  Char.ext_iff.mpr (UInt32.toNat_inj.mp h)

private theorem map_encodeChar_inj : ∀ (cs ds : List Char),
    cs.map encodeChar = ds.map encodeChar → cs = ds
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp [List.map] at h
  | _ :: _, [] => fun h => by simp [List.map] at h
  | c :: cs', d :: ds' => fun h => by
      simp only [List.map, List.cons.injEq] at h
      rw [encodeChar_inj h.1, map_encodeChar_inj cs' ds' h.2]

def encodeString (s : String) : Nat :=
  encodeList (s.toList.map encodeChar)

theorem encodeString_inj {s t : String} (h : encodeString s = encodeString t) : s = t :=
  String.ext (map_encodeChar_inj _ _ (encodeList_inj h))

-- ============================================================
-- Term / List Term encoding (mutual)
-- Uses definitional equality casts instead of simp (mutual defs
-- are not automatically unfolded by simp).
-- ============================================================

mutual
def encodeTerm : Term → Nat
  | .bvar n => npair 0 n
  | .fvar s => npair 1 (encodeString s)
  | .func s ts => npair 2 (npair (encodeString s) (encodeTerms ts))

def encodeTerms : List Term → Nat
  | [] => 0
  | t :: ts => npair (encodeTerm t) (encodeTerms ts) + 1
end

-- Cast h through definitional equality to expose npair structure.
-- (simp doesn't unfold mutual defs; direct type ascription does.)
mutual
theorem encodeTerm_inj : ∀ {t t' : Term}, encodeTerm t = encodeTerm t' → t = t'
  | .bvar n, .bvar n', h => by
      have h' : npair 0 n = npair 0 n' := h
      have hb := (npair_inj h').2
      rw [hb]
  | .bvar n, .fvar s, h => by
      have h' : npair 0 n = npair 1 (encodeString s) := h
      have htag := (npair_inj h').1; omega
  | .bvar n, .func s ts, h => by
      have h' : npair 0 n = npair 2 (npair (encodeString s) (encodeTerms ts)) := h
      have htag := (npair_inj h').1; omega
  | .fvar s, .bvar n, h => by
      have h' : npair 1 (encodeString s) = npair 0 n := h
      have htag := (npair_inj h').1; omega
  | .fvar s, .fvar s', h => by
      have h' : npair 1 (encodeString s) = npair 1 (encodeString s') := h
      have hs := (npair_inj h').2
      rw [encodeString_inj hs]
  | .fvar s, .func s' ts, h => by
      have h' : npair 1 (encodeString s) = npair 2 (npair (encodeString s') (encodeTerms ts)) := h
      have htag := (npair_inj h').1; omega
  | .func s ts, .bvar n, h => by
      have h' : npair 2 (npair (encodeString s) (encodeTerms ts)) = npair 0 n := h
      have htag := (npair_inj h').1; omega
  | .func s ts, .fvar s', h => by
      have h' : npair 2 (npair (encodeString s) (encodeTerms ts)) = npair 1 (encodeString s') := h
      have htag := (npair_inj h').1; omega
  | .func s ts, .func s' ts', h => by
      have h' : npair 2 (npair (encodeString s) (encodeTerms ts)) =
                npair 2 (npair (encodeString s') (encodeTerms ts')) := h
      have h2 := (npair_inj h').2
      have hs := (npair_inj h2).1
      have hts := (npair_inj h2).2
      rw [encodeString_inj hs, encodeTerms_inj hts]

theorem encodeTerms_inj : ∀ {ts ts' : List Term}, encodeTerms ts = encodeTerms ts' → ts = ts'
  | [], [], _ => rfl
  | [], t' :: ts', h => by
      have h' : (0 : Nat) = npair (encodeTerm t') (encodeTerms ts') + 1 := h
      omega
  | t :: ts, [], h => by
      have h' : npair (encodeTerm t) (encodeTerms ts) + 1 = 0 := h
      omega
  | t :: ts, t' :: ts', h => by
      have h' : npair (encodeTerm t) (encodeTerms ts) + 1 =
                npair (encodeTerm t') (encodeTerms ts') + 1 := h
      have heq : npair (encodeTerm t) (encodeTerms ts) =
                 npair (encodeTerm t') (encodeTerms ts') := by omega
      obtain ⟨ht, hts⟩ := npair_inj heq
      rw [encodeTerm_inj ht, encodeTerms_inj hts]
end

-- ============================================================
-- Formula encoding
-- Tags: bottom=0, eq=1, atom=2, impl=3, forall=4, and=5, or=6, ex=7
-- encodeFormula is NOT mutual so simp can unfold it normally.
-- ============================================================

def encodeFormula : Formula → Nat
  | .bottom => npair 0 0
  | .eq t1 t2 => npair 1 (npair (encodeTerm t1) (encodeTerm t2))
  | .atom p ts => npair 2 (npair (encodeString p) (encodeTerms ts))
  | .impl f g => npair 3 (npair (encodeFormula f) (encodeFormula g))
  | .forall f => npair 4 (encodeFormula f)
  | .and f g => npair 5 (npair (encodeFormula f) (encodeFormula g))
  | .or f g => npair 6 (npair (encodeFormula f) (encodeFormula g))
  | .ex f => npair 7 (encodeFormula f)

theorem encodeFormula_inj : ∀ {f g : Formula}, encodeFormula f = encodeFormula g → f = g
  | .bottom, .bottom, _ => rfl
  | .bottom, .eq _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .bottom, .atom _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .bottom, .impl _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .bottom, .forall _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .bottom, .and _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .bottom, .or _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .bottom, .ex _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .eq _ _, .bottom, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .eq t1 t2, .eq t1' t2', h => by
      simp only [encodeFormula] at h
      have h2 := (npair_inj h).2
      rw [encodeTerm_inj (npair_inj h2).1, encodeTerm_inj (npair_inj h2).2]
  | .eq _ _, .atom _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .eq _ _, .impl _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .eq _ _, .forall _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .eq _ _, .and _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .eq _ _, .or _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .eq _ _, .ex _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .atom _ _, .bottom, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .atom _ _, .eq _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .atom p ts, .atom p' ts', h => by
      simp only [encodeFormula] at h
      have h2 := (npair_inj h).2
      rw [encodeString_inj (npair_inj h2).1, encodeTerms_inj (npair_inj h2).2]
  | .atom _ _, .impl _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .atom _ _, .forall _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .atom _ _, .and _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .atom _ _, .or _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .atom _ _, .ex _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .impl _ _, .bottom, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .impl _ _, .eq _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .impl _ _, .atom _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .impl f1 f2, .impl g1 g2, h => by
      simp only [encodeFormula] at h
      have h2 := (npair_inj h).2
      rw [encodeFormula_inj (npair_inj h2).1, encodeFormula_inj (npair_inj h2).2]
  | .impl _ _, .forall _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .impl _ _, .and _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .impl _ _, .or _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .impl _ _, .ex _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .forall _, .bottom, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .forall _, .eq _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .forall _, .atom _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .forall _, .impl _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .forall f1, .forall g1, h => by
      simp only [encodeFormula] at h
      rw [encodeFormula_inj (npair_inj h).2]
  | .forall _, .and _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .forall _, .or _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .forall _, .ex _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .and _ _, .bottom, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .and _ _, .eq _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .and _ _, .atom _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .and _ _, .impl _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .and _ _, .forall _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .and f1 f2, .and g1 g2, h => by
      simp only [encodeFormula] at h
      have h2 := (npair_inj h).2
      rw [encodeFormula_inj (npair_inj h2).1, encodeFormula_inj (npair_inj h2).2]
  | .and _ _, .or _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .and _ _, .ex _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .or _ _, .bottom, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .or _ _, .eq _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .or _ _, .atom _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .or _ _, .impl _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .or _ _, .forall _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .or _ _, .and _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .or f1 f2, .or g1 g2, h => by
      simp only [encodeFormula] at h
      have h2 := (npair_inj h).2
      rw [encodeFormula_inj (npair_inj h2).1, encodeFormula_inj (npair_inj h2).2]
  | .or _ _, .ex _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .ex _, .bottom, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .ex _, .eq _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .ex _, .atom _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .ex _, .impl _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .ex _, .forall _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .ex _, .and _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .ex _, .or _ _, h => by
      simp only [encodeFormula] at h; exact absurd (npair_inj h).1 (by omega)
  | .ex f1, .ex g1, h => by
      simp only [encodeFormula] at h
      rw [encodeFormula_inj (npair_inj h).2]

-- ============================================================
-- formula_enum and formula_enum_surj (no axioms)
-- ============================================================

noncomputable def formula_enum (n : Nat) : Formula :=
  open Classical in
  if h : ∃ f : Formula, encodeFormula f = n
  then Classical.choose h
  else .bottom

theorem formula_enum_surj (f : Formula) : ∃ n, formula_enum n = f := by
  refine ⟨encodeFormula f, ?_⟩
  show (open Classical in
    if h : ∃ g : Formula, encodeFormula g = encodeFormula f
    then Classical.choose h
    else Formula.bottom) = f
  have hEx : ∃ g : Formula, encodeFormula g = encodeFormula f := ⟨f, rfl⟩
  simp only [hEx, ↓reduceDIte]
  exact encodeFormula_inj (Classical.choose_spec hEx)

end FOL.Util.Encoding

export FOL.Util.Encoding (
  npair npair_inj
  encodeList encodeList_inj
  encodeChar encodeChar_inj
  encodeString encodeString_inj
  encodeTerm encodeTerms encodeTerm_inj encodeTerms_inj
  encodeFormula encodeFormula_inj
  formula_enum formula_enum_surj
)
