/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.OrdinaryTime.FullWord
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.OrdinaryTime.CkAccelResidual
public import CollatzPosDens.OrdinaryTime.CkCountSmall
public import CollatzPosDens.OrdinaryTime.CkLengthGuard
public import CollatzPosDens.OrdinaryTime.CkScaleLast
public import CollatzPosDens.OrdinaryTime.LogSourceLower
public import CollatzPosDens.OrdinaryTime.Bstar
public import CollatzPosDens.OrdinaryTime.LogFourThirds
public import CollatzPosDens.OrdinaryTime.SelectedPair
public import CollatzPosDens.OrdinaryTime.Wstar
public import CollatzPosDens.OrdinaryTime.Telescope
public import CollatzPosDens.OrdinaryTime.ValuationLower
public import CollatzPosDens.OrdinaryTime.WidthSum
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Terminal.Sources

/-!
# The ordinary-time constant

Let `M` be a good seed, `n ≥ 2 · 10^10`, `X > 0`, and `(h, w)` a selected pair of level
`(M, n, X)` with full word `𝐰` of length `d` and source `x`. Then `d + 1 ≤ κ log x` with
`κ = 34881/10000`.

The proof combines the telescoping upper bound and the valuation lower bound on `A(𝐰) log 2`,
which give `γ (d + 1) ≤ log x - log M + g W_*(n) + (2n + 1) log 2 + (b_n/8) log 2 + γ`
with `g = log (4/3)`, `γ = 2 log 2 - θ` and `θ = log (3 + 1/4096)`. The error terms are bounded
by `(g/9000 + 219/250000) B_*(n)` and by `log M`, and the source bound
`(28559/100000) B_*(n) ≤ log x` closes the estimate, the final numerical inequality being the
positivity of the residual of `ckAccelResidual_eq`.

## Main results

* `CollatzPosDens.length_fullWord_add_one_le_kappa_mul_log`:
  `d + 1 ≤ (34881/10000) log x`.

## Implementation notes

The constant `θ` is written out as `log (3 + 1/4096)`, matching the telescoping bound, and the
source `x` is the rational `selectedPairSource M h w`, cast to `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- `log (4/3) - 1/12288 ≤ 2 log 2 - log (3 + 1/4096) ≤ log (4/3)`. -/
private theorem kappa_gamma_bounds :
    log (4 / 3) - 1 / 12288 ≤ 2 * log 2 - log (3 + 1 / 4096) ∧
      2 * log 2 - log (3 + 1 / 4096) ≤ log (4 / 3) := by
  have h43 : log (4 / 3 : ℝ) = 2 * log 2 - log 3 := by
    rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    push_cast
    ring
  have hθ : log (3 + 1 / 4096 : ℝ) = log 3 + log (1 + 1 / 12288) := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  have h1 := log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / 12288 by norm_num)
  have h2 : 0 ≤ log (1 + 1 / 12288 : ℝ) := log_nonneg (by norm_num)
  constructor <;> linarith

/-- If `F - 1/12288 ≤ γ`, `0 < γ`, `0.287682 < F`, `0 ≤ B`, `(28559/100000) B ≤ ℓ` and
`γ (d + 1) ≤ ℓ + (F/9000 + 219/250000) B`, then `d + 1 ≤ (34881/10000) ℓ`. -/
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

/-- A good seed satisfies `36 log 2 ≤ log M`. -/
theorem GoodSeed.thirty_six_mul_log_two_le_log {M : ℕ} (hM : GoodSeed M) :
    36 * log 2 ≤ log (M : ℝ) := by
  have := log_le_log (by positivity)
    (show (16 : ℝ) ^ scale 0 ≤ M by exact_mod_cast hM.lower.le)
  rw [log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow, scale_zero] at this
  push_cast at this
  linarith

/-- **The ordinary-time constant**. Let `M` be a good seed, `n ≥ 2 · 10^10`,
`X > 0`, and `(h, w)` a selected pair of level `(M, n, X)` with full word `𝐰` of length `d` and
source `x`. Then `d + 1 ≤ κ log x` with `κ = 34881/10000`. -/
@[collatz_pos_dens "lem_kappa"]
theorem length_fullWord_add_one_le_kappa_mul_log {M : ℕ} (hM : GoodSeed M) {n : ℕ}
    (hn : 2 * 10 ^ 10 ≤ n) {X : ℝ} (hX : 0 < X) {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X M h w) :
    ((fullWord h w).length + 1 : ℝ) ≤
      (34881 / 10000 : ℝ) * log (selectedPairSource M h w : ℝ) := by
  have htel := valSum_fullWord_mul_log_two_le hM hX hp
  have hval := valSum_fullWord_mul_log_two_ge hp
  obtain ⟨z, hz⟩ := hp.exists_intCast_eq_selectedPairSource
  have hlogx := le_log_of_mem_sources hM hn X (src_mem_sources (p := (h, w)) hp hz)
  rw [hz, Rat.cast_intCast] at htel ⊢
  have hWB : 9000 * (widthSum n : ℝ) ≤ scaleSum n := by
    exact_mod_cast nine_thousand_mul_widthSum_le_scaleSum n hn
  have hN : (2 ^ 22 * (n + 1) : ℝ) ≤ scaleSum n := by
    exact_mod_cast two_pow_twentyTwo_mul_succ_le_scaleSum n hn
  obtain ⟨hγlo, hγhi⟩ := kappa_gamma_bounds
  set ℓ := log (z : ℝ)
  set d : ℝ := ((fullWord h w).length : ℝ)
  set L := log 2
  set F := log (4 / 3)
  set B : ℝ := (scaleSum n : ℝ)
  set W : ℝ := (widthSum n : ℝ)
  set γ := 2 * L - log (3 + 1 / 4096) with hγ
  have hLpos : 0 < L := log_pos one_lt_two
  have hL7 : L < 347 / 500 := by
    have := log_two_bounds.2
    norm_num at this ⊢
    linarith
  have hF0 : (287682 / 10 ^ 6 : ℝ) < F := log_four_thirds_gt
  have hFL : F ≤ L := log_le_log (by norm_num) (by norm_num)
  have hγpos : 0 < γ := by linarith
  have hB0 : 0 ≤ B := by positivity
  have p1 : F * W ≤ F * (B / 9000) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have p2 : (2 * n + 1 + n / 4 : ℝ) * L ≤ 9 / 4 * (n + 1) * (347 / 500) := by
    have : (2 * n + 1 + n / 4 : ℝ) ≤ 9 / 4 * (n + 1) := by linarith
    calc (2 * n + 1 + n / 4 : ℝ) * L ≤ 9 / 4 * (n + 1) * L :=
          mul_le_mul_of_nonneg_right this hLpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hL7.le (by positivity)
  have p2' : 9 / 4 * (n + 1) * (347 / 500 : ℝ) ≤ B / 10 ^ 6 := by
    have h1 : (n + 1 : ℝ) ≤ B / 2 ^ 22 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 9 / 4 * (347 / 500) by norm_num)
    have h3 := mul_le_mul_of_nonneg_right ck_length_guard.le hB0
    linarith
  have p3 : (scale n : ℝ) * L ≤ (9 + B / 100 + 2 * n) * L :=
    mul_le_mul_of_nonneg_right (scale_le_scaleSum_div_hundred (by omega)) hLpos.le
  have p4 : B * L ≤ B * (7 / 10) := mul_le_mul_of_nonneg_left (by linarith) hB0
  have hstep : γ * (d + 1) ≤ ℓ + (F / 9000 + 219 / 250000) * B := by
    have s1 : (2 * L - log (3 + 1 / 4096)) * d ≤
        ℓ - log M + F * W + (2 * n + 1) * L + scale n / 8 * L := by
      linarith only [htel, hval]
    rw [hγ]
    linarith only [s1, p1, p2, p2', p3, p4, hγhi, hγ, hFL, hLpos,
      hM.thirty_six_mul_log_two_le_log]
  exact kappa_absorb hγlo hγpos hF0 hB0 hlogx hstep

end CollatzPosDens
