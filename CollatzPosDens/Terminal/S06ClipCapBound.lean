/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxDegreeOffsetPacking
public import CollatzPosDens.Terminal.S06ClipDensity
public import CollatzPosDens.Terminal.S06ClipFloorCap

/-!
# The clipped subdensity is bounded

For every real `B > 0` and every `y ∈ G_m`, the clipped subdensity satisfies
`g^clp_{m,n,B}(y) ≤ B / 2`.

Write `w = w^clp_{m,n}`, `A₀ = A^clp_{m,B}` and `L = L^clp_{m,n,B}`. The clipping degree window
`I^clp_{m,n,B}` is a set of `D ≤ 2w + 1` consecutive integers, all at least `max(m, A₀)`, so
joint degree and real-offset packing bounds `g^clp_{m,n,B}(y)` by
`D L + 3^m ∑_{A ∈ I, A ≥ m} 2^{-A}`. The first term is at most `(2w + 1) L = B / 4`; the second is
at most `3^m · 2 · 2^{-A₀} ≤ B / 4` by summing the geometric series and the degree floor cap.

## Main results

* `CollatzPosDens.clipDensity_le_half`: `g^clp_{m,n,B}(y) ≤ B / 2`.
* `CollatzPosDens.clipWindow_eq_Ico`: the clipping degree window is an interval `[a, a + D)`.

## Implementation notes

The source assumes `m ≥ 1` and `n ≥ 2`; the bound holds for all `m, n ∈ ℕ` and is stated so.
An empty window needs no separate case: it is the interval `[a, a + 0)`.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping degree window is the integer interval `[a, a + D)` with
`a = max(2m - w, max(m, A^clp_{m,B}))` and `D = (2m + w + 1 - a)⁺`, `w = w^clp_{m,n}`. -/
theorem clipWindow_eq_Ico (m n : ℕ) (B : ℝ) :
    clipWindow m n B =
      Finset.Ico (max (2 * m - clipWidth m n : ℤ) (max (m : ℤ) (clipFloor m B)))
        (max (2 * m - clipWidth m n : ℤ) (max (m : ℤ) (clipFloor m B)) +
          ((2 * m + clipWidth m n + 1 : ℤ) -
            max (2 * m - clipWidth m n : ℤ) (max (m : ℤ) (clipFloor m B))).toNat) := by
  ext A
  simp only [mem_clipWindow, Finset.mem_Ico, max_le_iff]
  omega

/-- The dyadic sum over an integer interval: `∑_{A ∈ [a, a + D)} 2^{-A} + 2 · 2^{-(a + D)}`
equals `2 · 2^{-a}`. -/
theorem sum_Ico_two_zpow_neg_add (a : ℤ) (D : ℕ) :
    ∑ A ∈ Finset.Ico a (a + D), (2 : ℝ) ^ (-A) + 2 * 2 ^ (-(a + D)) = 2 * 2 ^ (-a) := by
  induction D with
  | zero => simp
  | succ D ih =>
    have hins : Finset.Ico a (a + (D + 1 : ℕ)) = insert (a + D) (Finset.Ico a (a + D)) := by
      ext A
      simp only [Finset.mem_Ico, Finset.mem_insert]
      push_cast
      omega
    have hnot : a + D ∉ Finset.Ico a (a + D) := by simp
    rw [hins, Finset.sum_insert hnot, ← ih]
    have h2 : (2 : ℝ) ^ (-(a + D)) = 2 * 2 ^ (-(a + (D + 1 : ℕ))) := by
      rw [show -(a + D) = 1 + -(a + (D + 1 : ℕ)) by push_cast; ring,
        zpow_add₀ two_ne_zero, zpow_one]
    rw [h2]
    ring

/-- The dyadic sum over an integer interval starting at `a` is at most `2 · 2^{-a}`. -/
theorem sum_Ico_two_zpow_neg_le (a : ℤ) (D : ℕ) :
    ∑ A ∈ Finset.Ico a (a + D), (2 : ℝ) ^ (-A) ≤ 2 * 2 ^ (-a) := by
  rw [← sum_Ico_two_zpow_neg_add a D]
  have : (0 : ℝ) < 2 ^ (-(a + D)) := zpow_pos two_pos _
  linarith

/-- **The clipped subdensity is bounded.** For every real `B > 0` and every `y ∈ G_m`,
`g^clp_{m,n,B}(y) ≤ B / 2`. -/
@[collatz_pos_dens "lem_s06_clip_cap_bound"]
theorem clipDensity_le_half (m n : ℕ) {B : ℝ} (hB : 0 < B) (y : ResidueGroup m) :
    clipDensity m n B y ≤ B / 2 := by
  set a : ℤ := max (2 * m - clipWidth m n : ℤ) (max (m : ℤ) (clipFloor m B)) with ha
  set D : ℕ := ((2 * m + clipWidth m n + 1 : ℤ) - a).toNat with hD
  set L : ℝ := clipCap m n B with hL
  have hwin : clipWindow m n B = Finset.Ico a (a + D) := clipWindow_eq_Ico m n B
  have hL0 : 0 ≤ L := clipCap_nonneg m n hB.le
  have hset : {u | u ∈ clipWords m n B ∧ dyadicRed m ⟨off u, off_mem_dyadicRationals u⟩ = y} =
      {u : Word | u.length = m ∧ dyadicRed m ⟨off u, off_mem_dyadicRationals u⟩ = y ∧
        (u.valSum : ℤ) ∈ Finset.Ico a (a + D) ∧ (off u : ℝ) ≤ L} := by
    ext u
    simp only [mem_clipWords, hwin, Set.mem_ofPred_eq, hL]
    tauto
  have hpack := three_pow_mul_geomMass_degreeOffsetPacking_le m a D hL0 y
  rw [← hset, ← subMass_def] at hpack
  set S : ℝ := ∑ A ∈ Finset.Ico a (a + D) with (m : ℤ) ≤ A, (2 : ℝ) ^ (-A) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun A _ => (zpow_pos two_pos _).le
  have hmain : clipDensity m n B y ≤ D * L + 3 ^ m * S := by
    have h := ENNReal.toReal_le_of_le_ofReal (by positivity) hpack
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h
    rw [clipDensity_def]
    exact h
  have hDle : (D : ℝ) ≤ 2 * clipWidth m n + 1 := by
    have hcard := card_clipWindow_le m n B
    rw [hwin, Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] at hcard
    exact_mod_cast hcard
  have hDL : (D : ℝ) * L ≤ B / 4 := by
    have h := mul_clipCap m n B
    calc (D : ℝ) * L ≤ (2 * clipWidth m n + 1) * L := mul_le_mul_of_nonneg_right hDle hL0
      _ = B / 4 := by rw [hL]; linarith
  have hSle : S ≤ 2 * 2 ^ (-clipFloor m B) := by
    have ha0 : clipFloor m B ≤ a := (le_max_right _ _).trans (le_max_right _ _)
    calc S ≤ ∑ A ∈ Finset.Ico a (a + D), (2 : ℝ) ^ (-A) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun A _ _ => (zpow_pos two_pos _).le
      _ ≤ 2 * 2 ^ (-a) := sum_Ico_two_zpow_neg_le a D
      _ ≤ 2 * 2 ^ (-clipFloor m B) := by
          gcongr
          norm_num
  have hcap := three_pow_mul_two_zpow_neg_clipFloor_le m hB
  have hS3 : (3 : ℝ) ^ m * S ≤ B / 4 := by
    calc (3 : ℝ) ^ m * S ≤ 3 ^ m * (2 * 2 ^ (-clipFloor m B)) := by gcongr
      _ = 2 * (3 ^ m * 2 ^ (-clipFloor m B)) := by ring
      _ ≤ 2 * (B / 8) := by gcongr
      _ = B / 4 := by ring
  linarith

end CollatzPosDens
