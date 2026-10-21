/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Bstar
public import CollatzPosDens.Transfer.S02DFHead
public import CollatzPosDens.Transfer.S02AtanhBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The binary logarithm of the Fourier prefactor

We enclose the binary logarithm of the Fourier prefactor `B_F(ι) = Y^{A_*(ι)}`, where
`Y = 15/2 · D_F(ι)`, at both Fourier parameter indices:
$$\frac{3257939550287}{10^{10}} < \log_2 B_{\mathrm F}(\mathrm o) < \frac{3257939550288}{10^{10}},
\qquad
\frac{881188851176}{10^{10}} < \log_2 B_{\mathrm F}(\mathrm b) < \frac{881188851177}{10^{10}}.$$

Write `Y = u · 2^e`, with `e = 153` for `ι = o` and `e = 51` for `ι = b`; the leading binary
digits `𝖺` of `15 D_F(ι)` place `u` in the short interval `[𝖺/2^{79}, (𝖺 + 1)/2^{79}]` inside
`[1, 2]`. Since `log B_F(ι) = A_*(ι) log Y` and `log Y = e log 2 + log u`,
$$\log_2 B_{\mathrm F}(ι) = A_*(ι) \Bigl(e + \frac{\log u}{\log 2}\Bigr),$$
and the two logarithms `log 2` and `log u` are enclosed by partial sums of the inverse
hyperbolic tangent series.

## Main results

* `CollatzPosDens.logb_two_fourierPrefactor_mem_o`,
  `CollatzPosDens.logb_two_fourierPrefactor_mem_b`: the enclosures of `log₂ B_F(ι)`.

## Implementation notes

The two cases of the statement are the two theorems `logb_two_fourierPrefactor_mem_o` and
`logb_two_fourierPrefactor_mem_b`. Rather than evaluating the series at
`u^± = (𝖺 + {0,1})/2^{79}` with `80` terms, `u^-` and `u^+` are first replaced by continued
fraction convergents, `5684999/3434279 ≤ u^-` and `u^+ ≤ 269456/162777` for `ι = o`,
`24685979/13842011 ≤ u^-` and `u^+ ≤ 34420868/19300593` for `ι = b`, and each series is
truncated after at most `16` terms, the partial sums being rounded outward to sixteen decimal
places. The resulting enclosures still lie strictly inside the target intervals.
-/

@[expose] public section

namespace CollatzPosDens

open Real

private theorem log2Bstar_log_two :
    (6931471805599452 / 10 ^ 16 : ℝ) ≤ log 2 ∧ log 2 ≤ 6931471805599454 / 10 ^ 16 := by
  obtain ⟨h1, h2⟩ := log_mem_atanh_partialSum (y := (2 : ℝ)) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

private theorem log2Bstar_log_lower_o :
    (5040239457602595 / 10 ^ 16 : ℝ) ≤ log (5684999 / 3434279) := by
  obtain ⟨h1, -⟩ := log_mem_atanh_partialSum (y := (5684999 / 3434279 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h1
  linarith

private theorem log2Bstar_log_upper_o :
    log (269456 / 162777) ≤ (5040239457672018 / 10 ^ 16 : ℝ) := by
  obtain ⟨-, h2⟩ := log_mem_atanh_partialSum (y := (269456 / 162777 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h2
  linarith

private theorem log2Bstar_log_lower_b :
    (5785271875345510 / 10 ^ 16 : ℝ) ≤ log (24685979 / 13842011) := by
  obtain ⟨h1, -⟩ := log_mem_atanh_partialSum (y := (24685979 / 13842011 : ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ] at h1
  linarith

private theorem log2Bstar_log_upper_b :
    log (34420868 / 19300593) ≤ (5785271875345737 / 10 ^ 16 : ℝ) := by
  obtain ⟨-, h2⟩ := log_mem_atanh_partialSum (y := (34420868 / 19300593 : ℝ)) (by norm_num) 11
  norm_num [Finset.sum_range_succ] at h2
  linarith

/-- From `𝖺 · 2P ≤ 15 X < (𝖺 + 1) · 2P` and `c⁻ · 2^79 ≤ 𝖺`, `𝖺 + 1 ≤ c⁺ · 2^79`, the scaled
number `15/2 · X` lies in `[c⁻ · 2^79 P, c⁺ · 2^79 P]`. -/
private theorem log2Bstar_scaled_mem {X a cl cu P : ℝ} (hP : 0 ≤ P) (h1 : a * (2 * P) ≤ 15 * X)
    (h2 : 15 * X < (a + 1) * (2 * P)) (hcl : cl * 2 ^ 79 ≤ a) (hcu : a + 1 ≤ cu * 2 ^ 79) :
    cl * (2 ^ 79 * P) ≤ 15 / 2 * X ∧ 15 / 2 * X ≤ cu * (2 ^ 79 * P) := by
  have c₁ := mul_le_mul_of_nonneg_right hcl hP
  have c₂ := mul_le_mul_of_nonneg_right hcu hP
  constructor <;> nlinarith

/-- From `c⁻ 2^e ≤ Y ≤ c⁺ 2^e` with `c^± > 0`, the logarithm of `Y` lies in
`[log c⁻ + e log 2, log c⁺ + e log 2]`. -/
private theorem log2Bstar_log_mem {Y cl cu : ℝ} {e : ℕ} (hcl : 0 < cl) (hcu : 0 < cu)
    (h1 : cl * 2 ^ e ≤ Y) (h2 : Y ≤ cu * 2 ^ e) :
    log cl + e * log 2 ≤ log Y ∧ log Y ≤ log cu + e * log 2 := by
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have h₁ := log_le_log (by positivity) h1
  have h₂ := log_le_log hY h2
  rw [log_mul hcl.ne' (by positivity), log_pow] at h₁
  rw [log_mul hcu.ne' (by positivity), log_pow] at h₂
  exact ⟨h₁, h₂⟩

/-- **Binary logarithm of the Fourier prefactor at `ι = o`.**
`3257939550287/10^10 < log₂ B_F(o) < 3257939550288/10^10`. -/
@[collatz_pos_dens "lem_s02_log2Bstar"]
theorem logb_two_fourierPrefactor_mem_o :
    (3257939550287 / 10 ^ 10 : ℝ) < logb 2 (fourierPrefactor .o) ∧
      logb 2 (fourierPrefactor .o) < 3257939550288 / 10 ^ 10 := by
  obtain ⟨l2m, l2p⟩ := log2Bstar_log_two
  have la := log2Bstar_log_lower_o
  have lb := log2Bstar_log_upper_o
  obtain ⟨hX1, hX2⟩ := DF_head_o
  have h₁ : (1000609163609502169286000 : ℝ) * (2 * 2 ^ 74) ≤ 15 * (DF .o : ℝ) := by
    rw [← pow_succ']
    exact_mod_cast hX1
  have h₂ : 15 * (DF .o : ℝ) < (1000609163609502169286000 + 1) * (2 * 2 ^ 74) := by
    rw [← pow_succ']
    norm_num
    exact_mod_cast hX2
  obtain ⟨hY1, hY2⟩ := log2Bstar_scaled_mem (cl := 5684999 / 3434279)
    (cu := 269456 / 162777) (by positivity) h₁ h₂ (by norm_num) (by norm_num)
  rw [← pow_add] at hY1 hY2
  obtain ⟨hlogY1, hlogY2⟩ := log2Bstar_log_mem (by norm_num) (by norm_num) hY1 hY2
  have hl2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hlogB :
      log (fourierPrefactor .o) = 21193 / 10000 * log (15 / 2 * (DF .o : ℝ)) := by
    rw [fourierPrefactor_def, log_rpow (fourierPrefactor_base_pos .o), Aexp_cast_o]
  push_cast at hlogY1 hlogY2
  rw [logb, hlogB]
  constructor
  · rw [lt_div_iff₀ hl2]
    linarith
  · rw [div_lt_iff₀ hl2]
    linarith

/-- **Binary logarithm of the Fourier prefactor at `ι = b`.**
`881188851176/10^10 < log₂ B_F(b) < 881188851177/10^10`. -/
@[collatz_pos_dens "lem_s02_log2Bstar"]
theorem logb_two_fourierPrefactor_mem_b :
    (881188851176 / 10 ^ 10 : ℝ) < logb 2 (fourierPrefactor .b) ∧
      logb 2 (fourierPrefactor .b) < 881188851177 / 10 ^ 10 := by
  obtain ⟨l2m, l2p⟩ := log2Bstar_log_two
  have la := log2Bstar_log_lower_b
  have lb := log2Bstar_log_upper_b
  obtain ⟨hX1, hX2⟩ := DF_head_b
  have h₁ : (1078005117737754427392000 : ℝ) / 2 ^ 27 ≤ 15 * (DF .b : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 hX1
    push_cast at h
    exact h
  have h₂ : 15 * (DF .b : ℝ) < (1078005117737754427392001 : ℝ) / 2 ^ 27 := by
    have h := (Rat.cast_lt (K := ℝ)).2 hX2
    push_cast at h
    exact h
  have hY1 : (24685979 / 13842011 : ℝ) * 2 ^ 51 ≤ 15 / 2 * (DF .b : ℝ) := by
    have : (24685979 / 13842011 : ℝ) * 2 ^ 51 ≤ (1078005117737754427392000 : ℝ) / 2 ^ 28 := by
      norm_num
    linarith
  have hY2 : 15 / 2 * (DF .b : ℝ) ≤ (34420868 / 19300593 : ℝ) * 2 ^ 51 := by
    have : (1078005117737754427392001 : ℝ) / 2 ^ 28 ≤ (34420868 / 19300593 : ℝ) * 2 ^ 51 := by
      norm_num
    linarith
  obtain ⟨hlogY1, hlogY2⟩ := log2Bstar_log_mem (by norm_num) (by norm_num) hY1 hY2
  have hl2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hlogB :
      log (fourierPrefactor .b) = 17 / 10 * log (15 / 2 * (DF .b : ℝ)) := by
    rw [fourierPrefactor_def, log_rpow (fourierPrefactor_base_pos .b), Aexp_cast_b]
  push_cast at hlogY1 hlogY2
  rw [logb, hlogB]
  constructor
  · rw [lt_div_iff₀ hl2]
    linarith
  · rw [div_lt_iff₀ hl2]
    linarith

end CollatzPosDens
