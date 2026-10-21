/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.OrdinaryTime.S07FullWord
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Recipe.SeedShift
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.OrdinaryTime.CkAccelResidual
public import CollatzPosDens.OrdinaryTime.CkCountSmall
public import CollatzPosDens.OrdinaryTime.CkLengthGuard
public import CollatzPosDens.OrdinaryTime.CkScaleLast
public import CollatzPosDens.OrdinaryTime.LogSourceLower
public import CollatzPosDens.OrdinaryTime.S07Bstar
public import CollatzPosDens.OrdinaryTime.S07LogFourThirds
public import CollatzPosDens.OrdinaryTime.S07SelectedPair
public import CollatzPosDens.OrdinaryTime.S07Wstar
public import CollatzPosDens.OrdinaryTime.Telescope
public import CollatzPosDens.OrdinaryTime.ValuationLower
public import CollatzPosDens.OrdinaryTime.WidthSum
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Terminal.Sources

/-!
# The ordinary-time constant

Let `t ≥ 1`, `t₁` a `t`-good seed, `n ≥ covGen`, `X` real, and `(h, w)` a selected pair of level
`(t₁, n, X)` with full word `fullWord h w` of length `d` and source
`x = selectedPairSource t₁ h w`. Then `d + 1 ≤ (34881/10000) log (x / t)`.

The proof combines the telescoping upper bound and the valuation lower bound on the valuation sum
of `fullWord h w` times `log 2`, which give
`γ (d + 1) ≤ log x - log t₁ + log (4/3) widthSum n + (2n + 1) log 2 + (scale n / 8) log 2 + γ`
with `γ = 2 log 2 - log (3 + 1/4096)`. The error terms are bounded by
`(log (4/3)/9000 + 219/250000) scaleSum n` and by `log t₁ - log t`, using
`t₁ > 2 ^ seedShift * t` (so also `targetFloor ≤ t₁`, as the telescoping bound needs), and the
source bound `(28559/100000) scaleSum n ≤ log (x / t)` closes the estimate, the final numerical
inequality being the positivity of the residual of `ckAccelResidual_eq`. The source is nonzero,
since otherwise the source bound would give `scaleSum n ≤ 0`.

## Main results

* `CollatzPosDens.length_fullWord_add_one_le_kappa_mul_log`:
  `d + 1 ≤ (34881/10000) log (x / t)`.

## Implementation notes

The constant `log 3 + log (1 + 1/12288)` is written out as `log (3 + 1/4096)`, matching the
telescoping bound, and the source `x` is the rational `selectedPairSource t₁ h w`, cast to `ℝ`;
`x / t` is real division. The statement holds for every real `X` and needs neither `X > 0` nor
`3 ∤ t`, so it is stated without them. Positivity of the source follows from the source bound
itself (a zero source would force `scaleSum n ≤ 0`), so the inverse-orbit description of the
source is not needed. A history of generation `n` is a tuple `Fin n → Word`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- `log (4/3) - 1/12288 ≤ c_gain ≤ log (4/3)`, where `c_gain = 2 log 2 - log (3 + 1/4096)`. -/
private theorem kappa_gamma_bounds :
    log (4 / 3) - 1 / 12288 ≤ 2 * log 2 - log (3 + 1 / 4096) ∧
      2 * log 2 - log (3 + 1 / 4096) ≤ log (4 / 3) := by
  have h43 : log (4 / 3 : ℝ) = 2 * log 2 - log 3 := by
    rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast; ring
  have hθ : log (3 + 1 / 4096 : ℝ) = log 3 + log (1 + 1 / 12288) := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  have h1 := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 12288 by norm_num)
  have h2 : 0 ≤ log (1 + 1 / 12288 : ℝ) := log_nonneg (by norm_num)
  constructor <;> linarith

/-- The final absorption step: from `c_gain (d + 1) ≤ ℓ + (F/9000 + 219/250000) B` and the source
bound `(28559/100000) B ≤ ℓ`, conclude `d + 1 ≤ (34881/10000) ℓ`. -/
private theorem kappa_absorb {γ ℓ F B d : ℝ} (hγlo : F - 1 / 12288 ≤ γ)
    (hγpos : 0 < γ) (hF0 : 287682 / 10 ^ 6 < F) (hB0 : 0 ≤ B)
    (hℓ : 28559 / 100000 * B ≤ ℓ)
    (hstep : γ * (d + 1) ≤ ℓ + (F / 9000 + 219 / 250000) * B) :
    d + 1 ≤ 34881 / 10000 * ℓ := by
  have hres := ckAccelResidual_eq (K := ℝ)
  have q1 : (F / 9000 + 219 / 250000) * B ≤
      (F / 9000 + 219 / 250000) * (100000 / 28559 * ℓ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have q2 : (1 + (F / 9000 + 219 / 250000) * (100000 / 28559)) * ℓ ≤
      34881 / 10000 * γ * ℓ :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  exact le_of_mul_le_mul_right (by linarith : (d + 1) * γ ≤ 34881 / 10000 * ℓ * γ) hγpos

/-- Let `t ≥ 1`, `t₁` a `t`-good seed, `n ≥ covGen`, `X` real, and `(h, w)` a selected pair of
level `(t₁, n, X)` with source `x = selectedPairSource t₁ h w`. Then the length `d` of
`fullWord h w` satisfies `d + 1 ≤ (34881/10000) log (x / t)`. -/
@[collatz_pos_dens "lem_kappa"]
theorem length_fullWord_add_one_le_kappa_mul_log {t t₁ : ℕ} (ht₁ : GoodSeed t t₁) (ht : 0 < t)
    {n : ℕ} (hn : covGen ≤ n) {X : ℝ} {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X t₁ h w) :
    ((fullWord h w).length + 1 : ℝ) ≤
      (34881 / 10000 : ℝ) * log ((selectedPairSource t₁ h w : ℝ) / t) := by
  have hσ : (2 : ℕ) ^ seedShift = targetFloor := by
    rw [seedShift_def, targetFloor_def, pow_mul, show (2 : ℕ) ^ 4 = 16 from rfl]
  have ht₁floor : targetFloor ≤ t₁ := by
    rw [← hσ]
    exact (Nat.le_mul_of_pos_right _ ht).trans ht₁.lower.le
  have hp' : IsSelectedPair n X ((t₁ : ℤ) : ℚ) h w := by rwa [Int.cast_natCast]
  have htel := valSum_fullWord_mul_log_two_le (by exact_mod_cast ht₁.odd)
    (by exact_mod_cast ht₁floor) hp'
  simp only [Int.cast_natCast] at htel
  have hval := valSum_fullWord_mul_log_two_ge hp
  obtain ⟨z, hz⟩ := hp.exists_intCast_eq_selectedPairSource
  have hlogx := le_log_of_mem_sources ht ht₁ hn X (src_mem_sources (p := (h, w)) hp hz)
  rw [hz, Rat.cast_intCast] at htel ⊢
  have hWB : 9000 * (widthSum n : ℝ) ≤ scaleSum n := by
    exact_mod_cast nine_thousand_mul_widthSum_le_scaleSum n hn
  have hN : (2 ^ 22 * (n + 1) : ℝ) ≤ scaleSum n := by
    exact_mod_cast two_pow_twentyTwo_mul_succ_le_scaleSum n hn
  have hbn := scale_le_scaleSum_div_hundred n
  have hguard := ckLengthGuard
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hlogt₁ : 66176 * log 2 ≤ log t₁ - log t := by
    have h2 : (2 : ℝ) ^ seedShift * t ≤ t₁ := by exact_mod_cast ht₁.lower.le
    have := log_le_log (by positivity) h2
    rw [log_mul (by positivity) ht0.ne', log_pow, seedShift_eq] at this
    push_cast at this
    linarith
  have hBpos : (0 : ℝ) < scaleSum n :=
    lt_of_lt_of_le (by positivity) hN
  have hz0 : (z : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_div, log_zero] at hlogx
    linarith
  rw [log_div hz0 ht0.ne'] at hlogx ⊢
  obtain ⟨hγlo, hγhi⟩ := kappa_gamma_bounds
  set ℓ := log (z : ℝ) - log t with hℓ
  set d : ℝ := ((fullWord h w).length : ℝ)
  set L := log 2
  set F := log (4 / 3)
  set B : ℝ := (scaleSum n : ℝ)
  set W : ℝ := (widthSum n : ℝ)
  set γ := 2 * L - log (3 + 1 / 4096) with hγ
  have hLpos : 0 < L := log_pos one_lt_two
  have hL7 : L < 347 / 500 := by have := log_two_bounds.2; norm_num at this ⊢; linarith
  have hF0 : (287682 / 10 ^ 6 : ℝ) < F := log_four_thirds_gt
  have hFL : F ≤ L := log_le_log (by norm_num) (by norm_num)
  have hγpos : 0 < γ := by linarith
  have hB0 : 0 ≤ B := hBpos.le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have p1 : F * W ≤ F * (B / 9000) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have p2 : (2 * n + 1 + n / 8 : ℝ) * L ≤ 9 / 4 * (n + 1) * (347 / 500) := by
    have : (2 * n + 1 + n / 8 : ℝ) ≤ 9 / 4 * (n + 1) := by linarith
    calc (2 * n + 1 + n / 8 : ℝ) * L ≤ 9 / 4 * (n + 1) * L :=
          mul_le_mul_of_nonneg_right this hLpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hL7.le (by positivity)
  have p2' : 9 / 4 * (n + 1) * (347 / 500 : ℝ) ≤ B / 10 ^ 6 := by
    have h1 : (n + 1 : ℝ) ≤ B / 2 ^ 22 := by rw [le_div_iff₀ (by positivity)]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 9 / 4 * (347 / 500) by norm_num)
    have h3 := mul_le_mul_of_nonneg_right hguard.le hB0
    linarith
  have p3 : (scale n : ℝ) * L ≤ (16544 + B / 100 + n) * L :=
    mul_le_mul_of_nonneg_right hbn hLpos.le
  have p4 : B * L ≤ B * (7 / 10) := mul_le_mul_of_nonneg_left (by linarith) hB0
  have hstep : γ * (d + 1) ≤ ℓ + (F / 9000 + 219 / 250000) * B := by
    have s1 : (2 * L - log (3 + 1 / 4096)) * d ≤
        log (z : ℝ) - log t₁ + F * W + (2 * n + 1) * L + scale n / 8 * L := by
      linarith only [htel, hval]
    rw [hγ]
    linarith only [s1, p1, p2, p2', p3, p4, hγhi, hγ, hFL, hlogt₁, hLpos, hℓ]
  exact kappa_absorb hγlo hγpos hF0 hB0 hlogx hstep

end CollatzPosDens
