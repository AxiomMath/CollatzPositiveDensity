/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhEjSplit
public import CollatzPosDens.Recipe.PhTailMainRatio
public import CollatzPosDens.Recipe.PhTailMainStart
public import CollatzPosDens.Seed.CentralIncrement
public import CollatzPosDens.FirstCrossing.PhDeltaBounds

/-!
# A geometric bound for the propagation majorant

Let `N_* = 9853` be the generation threshold and `𝗀 = 101/100` the physical growth ratio. For
every `j ≥ N_*`, the propagation majorant satisfies
$$\mathsf E_j\le\frac{7584}{10^6}\Bigl(\frac{990945}{10^6}\Bigr)^{j-N_*}
  +2^{-90}\Bigl(\frac{199}{200}\Bigr)^{j-N_*}.$$

The proof starts from the splitting
`E_j ≤ E^mx_j + 2^8 j^{5/2} 𝗀^{-j} + 2^{-20} j^{5/2} θ^j`, with `θ = 𝗀^{1/2} 2^{-1/56}`, and
bounds each term by a geometric sequence started at `N_*`:

* `E^mx_{N_*} < 7583/10^6` and `E^mx_{j+1} ≤ (990945/10^6) E^mx_j`;
* `N_*^{5/2} < 2^{34}`, from `N_*^5 < 2^{68}`, and `𝗀^{N_*} ≥ (𝗀^{70})^{140} > 2^{140}`, so
  `2^8 N_*^{5/2} 𝗀^{-N_*} < 2^{8+34-140} = 2^{-98} ≤ 1/10^6`; the ratio of consecutive terms,
  `(1 + 1/j)^{5/2} · 100/101`, is at most `990945/10^6` for `j ≥ N_*`: squared, this is
  `(j+1)^5 · 10^{16} ≤ j^5 · 100085445^2` (note `101 · 990945 = 100085445`), which follows from
  the exact comparison at `j = N_*` since `(1 + 1/j)^5` decreases;
* the ratio `(1 + 1/j)^{5/2} θ` is at most `199/200` for `j ≥ N_*`: raised to the `56`-th power,
  this is `(j+1)^{140} · 101^{28} · 200^{56} ≤ 2 · j^{140} · 100^{28} · 199^{56}`. At the start,
  write `N_* = 56 · 175 + 53`; since `θ ≤ 1` and `θ^{56} = 𝗀^{28}/2`,
  `θ^{N_*} ≤ (𝗀^{28}/2)^{175} ≤ 2^{-104}`, the last step being the exact comparison
  `101^{4900} · 2^{104} ≤ 2^{175} · 100^{4900}`. With `N_*^{5/2} < 2^{34}` this gives
  `2^{-20} N_*^{5/2} θ^{N_*} < 2^{-20+34-104} = 2^{-90}`.

Since `7583/10^6 + 1/10^6 = 7584/10^6`, adding the three bounds gives the claim. Combined with
the central increment bound `|Z_{j+1}(t) - Z_j(t)| ≤ E_j`, the same geometric bound holds for the
increments of the weighted central sum.

## Main results

* `CollatzPosDens.propagationMajorant_le_geometric`: the geometric bound for `E_j`; summed, it
  gives `CollatzPosDens.sum_Ico_generationThreshold_propagationMajorant_lt`.
* `CollatzPosDens.abs_weightedCentralSum_succ_sub_le_geometric`: the geometric bound for
  `|Z_{j+1}(t) - Z_j(t)|`, for odd positive `t`.

## Implementation notes

The powers `j^{5/2}`, `𝗀^{-j}` and `θ^j` are real powers of the casts, as in
`CollatzPosDens.propagationMajorant_le_split`; the geometric factors are natural-number powers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A sequence with `a N ≤ C` and `a (j+1) ≤ r a j` for `j ≥ N`, `0 ≤ r`, satisfies
`a j ≤ C r^{j-N}` for `j ≥ N`. -/
private lemma le_mul_pow_sub_of_succ_le {a : ℕ → ℝ} {C r : ℝ} {N : ℕ} (hr : 0 ≤ r)
    (h0 : a N ≤ C) (hs : ∀ j, N ≤ j → a (j + 1) ≤ r * a j) {j : ℕ} (hj : N ≤ j) :
    a j ≤ C * r ^ (j - N) := by
  induction j, hj using Nat.le_induction with
  | base => simpa using h0
  | succ j hj ih =>
    rw [Nat.sub_add_comm hj, pow_succ]
    calc a (j + 1) ≤ r * a j := hs j hj
      _ ≤ r * (C * r ^ (j - N)) := mul_le_mul_of_nonneg_left ih hr
      _ = C * (r ^ (j - N) * r) := by ring

/-- The square of `x^{5/2}` is `x^5`. -/
private lemma rpow_five_halves_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (5 / 2 : ℝ)) ^ 2 = x ^ 5 := by
  rw [← Real.rpow_natCast (x ^ (5 / 2 : ℝ)), ← Real.rpow_mul hx]
  norm_num

/-- The `56`-th power of `x^{5/2}` is `x^{140}`. -/
private lemma rpow_five_halves_pow_fiftySix {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (5 / 2 : ℝ)) ^ 56 = x ^ 140 := by
  rw [← Real.rpow_natCast (x ^ (5 / 2 : ℝ)), ← Real.rpow_mul hx]
  norm_num

/-- `N_*^{5/2} < 2^{34}`, from `N_*^5 < 2^{68}`. -/
private lemma generationThreshold_rpow_lt_two_pow :
    (generationThreshold : ℝ) ^ (5 / 2 : ℝ) < 2 ^ 34 := by
  have hcert : generationThreshold ^ 5 < 2 ^ 68 := by
    rw [generationThreshold_def]; decide +kernel
  have hR : (generationThreshold : ℝ) ^ 5 < 2 ^ 68 := by exact_mod_cast hcert
  refine (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero)).1 ?_
  rw [rpow_five_halves_sq (by positivity)]
  linarith

/-! ### The mixing term -/

/-- `E^mx_j ≤ (7583/10^6) (990945/10^6)^{j-N_*}` for `j ≥ N_*`. -/
private lemma propagationMixingMajorant_le_geometric {j : ℕ} (hj : generationThreshold ≤ j) :
    propagationMixingMajorant j ≤
      7583 / 10 ^ 6 * (990945 / 10 ^ 6 : ℝ) ^ (j - generationThreshold) :=
  le_mul_pow_sub_of_succ_le (by norm_num) propagationMixingMajorant_generationThreshold_lt.le
    (fun _ hj => propagationMixingMajorant_succ_le hj) hj

/-! ### The central term -/

/-- `(j+1)^5 · 10^{16} ≤ j^5 · 100085445^2` for `j ≥ N_*`. -/
private lemma central_ratio_nat {j : ℕ} (hj : generationThreshold ≤ j) :
    (j + 1) ^ 5 * 10 ^ 16 ≤ j ^ 5 * 100085445 ^ 2 := by
  rw [generationThreshold_def] at hj
  have hcert : (9853 + 1) ^ 5 * 10 ^ 16 < 9853 ^ 5 * 100085445 ^ 2 := by
    decide +kernel
  have hmono : (j + 1) ^ 5 * 9853 ^ 5 ≤ (9853 + 1) ^ 5 * j ^ 5 := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (by omega) 5
  have hpos : 0 < 9853 ^ 5 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (j + 1) ^ 5 * 10 ^ 16 * 9853 ^ 5
      = (j + 1) ^ 5 * 9853 ^ 5 * 10 ^ 16 := by ring
    _ ≤ (9853 + 1) ^ 5 * j ^ 5 * 10 ^ 16 := Nat.mul_le_mul_right _ hmono
    _ = j ^ 5 * ((9853 + 1) ^ 5 * 10 ^ 16) := by ring
    _ ≤ j ^ 5 * (9853 ^ 5 * 100085445 ^ 2) := Nat.mul_le_mul_left _ hcert.le
    _ = j ^ 5 * 100085445 ^ 2 * 9853 ^ 5 := by ring

/-- `(j+1)^{5/2} · 10^8 ≤ 100085445 · j^{5/2}` for `j ≥ N_*`. -/
private lemma central_ratio_real {j : ℕ} (hj : generationThreshold ≤ j) :
    ((j + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) * 10 ^ 8 ≤ 100085445 * (j : ℝ) ^ (5 / 2 : ℝ) := by
  have h := central_ratio_nat hj
  have hR : (((j + 1 : ℕ) : ℝ)) ^ 5 * 10 ^ 16 ≤ (j : ℝ) ^ 5 * 100085445 ^ 2 := by
    exact_mod_cast h
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero)).1 ?_
  rw [mul_pow, mul_pow, rpow_five_halves_sq (by positivity), rpow_five_halves_sq (by positivity)]
  nlinarith

/-- `𝗀^{-N_*} < 2^{-140}`, from `𝗀^{N_*} ≥ (𝗀^{70})^{140}` and `𝗀^{70} > 2`. -/
private lemma growthRatio_rpow_neg_generationThreshold_lt :
    (growthRatio : ℝ) ^ (-(generationThreshold : ℝ)) < 2 ^ (-140 : ℤ) := by
  have hg := growthRatio_cast_pos
  have h2 : (2 : ℝ) < (growthRatio : ℝ) ^ 70 := by rw [growthRatio_cast]; norm_num
  have h70 : (2 : ℝ) ^ 140 < (growthRatio : ℝ) ^ 9800 := by
    rw [show 9800 = 70 * 140 by norm_num, pow_mul]
    exact pow_lt_pow_left₀ h2 (by norm_num) (by norm_num)
  have hN : (growthRatio : ℝ) ^ 9800 ≤ (growthRatio : ℝ) ^ generationThreshold :=
    pow_le_pow_right₀ one_lt_growthRatio_cast.le (by rw [generationThreshold_def]; norm_num)
  rw [Real.rpow_neg hg.le, Real.rpow_natCast, zpow_neg, zpow_ofNat]
  exact inv_strictAnti₀ (by positivity) (h70.trans_le hN)

/-- `2^8 j^{5/2} 𝗀^{-j} ≤ (1/10^6) (990945/10^6)^{j-N_*}` for `j ≥ N_*`. -/
private lemma central_le_geometric {j : ℕ} (hj : generationThreshold ≤ j) :
    2 ^ 8 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ (-(j : ℝ)) ≤
      1 / 10 ^ 6 * (990945 / 10 ^ 6 : ℝ) ^ (j - generationThreshold) := by
  have hg := growthRatio_cast_pos
  refine le_mul_pow_sub_of_succ_le (a := fun j : ℕ =>
    2 ^ 8 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ (-(j : ℝ))) (by norm_num) ?_ ?_ hj
  · have h1 := generationThreshold_rpow_lt_two_pow
    have h2 := growthRatio_rpow_neg_generationThreshold_lt
    have hp : 0 < (growthRatio : ℝ) ^ (-(generationThreshold : ℝ)) := Real.rpow_pos_of_pos hg _
    have hq : 0 ≤ (generationThreshold : ℝ) ^ (5 / 2 : ℝ) := by positivity
    calc (2 : ℝ) ^ 8 * (generationThreshold : ℝ) ^ (5 / 2 : ℝ) *
          (growthRatio : ℝ) ^ (-(generationThreshold : ℝ))
        ≤ 2 ^ 8 * (2 ^ 34 * 2 ^ (-140 : ℤ)) := by
          rw [mul_assoc]; gcongr
      _ = 2 ^ (-98 : ℤ) := by
          rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
          norm_num
      _ ≤ 1 / 10 ^ 6 := by norm_num
  · intro j hj
    have h := central_ratio_real hj
    change 2 ^ 8 * ((j + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) ≤
      990945 / 10 ^ 6 * (2 ^ 8 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ (-(j : ℝ)))
    have hsucc : (growthRatio : ℝ) ^ (-((j + 1 : ℕ) : ℝ)) =
        (growthRatio : ℝ) ^ (-(j : ℝ)) * (100 / 101) := by
      rw [Nat.cast_succ, neg_add, Real.rpow_add hg, Real.rpow_neg_one, growthRatio_cast]
      norm_num
    rw [hsucc]
    have hp : 0 < (growthRatio : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos hg _
    nlinarith

/-! ### The cap term -/

/-- `(j+1)^{140} · 101^{28} · 200^{56} ≤ 2 · j^{140} · 100^{28} · 199^{56}` for `j ≥ N_*`. -/
private lemma cap_ratio_nat {j : ℕ} (hj : generationThreshold ≤ j) :
    (j + 1) ^ 140 * (101 ^ 28 * 200 ^ 56) ≤ j ^ 140 * (2 * 100 ^ 28 * 199 ^ 56) := by
  rw [generationThreshold_def] at hj
  have hcert : (9853 + 1) ^ 140 * (101 ^ 28 * 200 ^ 56) <
      9853 ^ 140 * (2 * 100 ^ 28 * 199 ^ 56) := by
    decide +kernel
  have hmono : (j + 1) ^ 140 * 9853 ^ 140 ≤ (9853 + 1) ^ 140 * j ^ 140 := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (by omega) 140
  have hpos : 0 < 9853 ^ 140 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (j + 1) ^ 140 * (101 ^ 28 * 200 ^ 56) * 9853 ^ 140
      = (j + 1) ^ 140 * 9853 ^ 140 * (101 ^ 28 * 200 ^ 56) := by ring
    _ ≤ (9853 + 1) ^ 140 * j ^ 140 * (101 ^ 28 * 200 ^ 56) := Nat.mul_le_mul_right _ hmono
    _ = j ^ 140 * ((9853 + 1) ^ 140 * (101 ^ 28 * 200 ^ 56)) := by ring
    _ ≤ j ^ 140 * (9853 ^ 140 * (2 * 100 ^ 28 * 199 ^ 56)) := Nat.mul_le_mul_left _ hcert.le
    _ = j ^ 140 * (2 * 100 ^ 28 * 199 ^ 56) * 9853 ^ 140 := by ring

/-- The `56`-th power of `θ = 𝗀^{1/2} 2^{-1/56}` is `𝗀^{28}/2`. -/
private lemma capRatio_pow_fiftySix :
    ((growthRatio : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ))) ^ 56 =
      (101 / 100 : ℝ) ^ 28 / 2 := by
  rw [mul_pow, ← Real.rpow_natCast ((growthRatio : ℝ) ^ (1 / 2 : ℝ)),
    ← Real.rpow_mul growthRatio_cast_pos.le, ← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 56 : ℝ))),
    ← Real.rpow_mul (by norm_num), growthRatio_cast]
  norm_num [Real.rpow_neg_one]

/-- `(j+1)^{5/2} θ · 200 ≤ 199 · j^{5/2}` for `j ≥ N_*`. -/
private lemma cap_ratio_real {j : ℕ} (hj : generationThreshold ≤ j) :
    ((j + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) *
        ((growthRatio : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ))) * 200 ≤
      199 * (j : ℝ) ^ (5 / 2 : ℝ) := by
  have h := cap_ratio_nat hj
  have hR : (((j + 1 : ℕ) : ℝ)) ^ 140 * (101 ^ 28 * 200 ^ 56) ≤
      (j : ℝ) ^ 140 * (2 * 100 ^ 28 * 199 ^ 56) := by
    exact_mod_cast h
  have hθ : 0 ≤ (growthRatio : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ)) := by
    have := growthRatio_cast_pos; positivity
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (n := 56) (by norm_num)).1 ?_
  rw [show ∀ a b : ℝ, (a * b * 200) ^ 56 = a ^ 56 * b ^ 56 * 200 ^ 56 from fun a b => by ring,
    mul_pow (199 : ℝ), rpow_five_halves_pow_fiftySix (by positivity),
    rpow_five_halves_pow_fiftySix (by positivity), capRatio_pow_fiftySix]
  have h100 : (0 : ℝ) < 100 ^ 28 := by positivity
  rw [div_pow, div_div, mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- `θ^{N_*} ≤ 2^{-104}`, from `θ ≤ 1`, `θ^{56} = 𝗀^{28}/2` and
`101^{4900} · 2^{104} ≤ 2^{175} · 100^{4900}`. -/
private lemma capRatio_pow_generationThreshold_le :
    ((growthRatio : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ))) ^ generationThreshold ≤
      2 ^ (-104 : ℤ) := by
  set θ : ℝ := (growthRatio : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ)) with hθdef
  have hθ0 : 0 ≤ θ := by have := growthRatio_cast_pos; positivity
  have h56 : θ ^ 56 = (101 / 100 : ℝ) ^ 28 / 2 := capRatio_pow_fiftySix
  have hθ1 : θ ≤ 1 := by
    refine (pow_le_one_iff_of_nonneg hθ0 (n := 56) (by norm_num)).1 ?_
    rw [h56]; norm_num
  have hcert : (101 : ℕ) ^ 4900 * 2 ^ 104 ≤ 2 ^ 175 * 100 ^ 4900 := by decide +kernel
  have hR : ((101 : ℕ) : ℝ) ^ 4900 * (2 : ℝ) ^ 104 ≤ (2 : ℝ) ^ 175 * ((100 : ℕ) : ℝ) ^ 4900 := by
    exact_mod_cast hcert
  have key : ∀ x y : ℝ, 0 < y → x ^ 4900 * 2 ^ 104 ≤ 2 ^ 175 * y ^ 4900 →
      ((x / y) ^ 28 / 2) ^ 175 ≤ 2 ^ (-104 : ℤ) := by
    intro x y hy hxy
    have e : ((x / y) ^ 28 / 2) ^ 175 = x ^ 4900 / (y ^ 4900 * 2 ^ 175) := by
      field_simp
    rw [e, zpow_neg, zpow_ofNat, div_le_iff₀ (by positivity)]
    rw [show (2 : ℝ) ^ 175 = 2 ^ 104 * 2 ^ 71 by rw [← pow_add]] at hxy ⊢
    have h104 : (0 : ℝ) < 2 ^ 104 := by positivity
    rw [inv_mul_eq_div, le_div_iff₀ h104]
    linarith
  have h175 : θ ^ (56 * 175) ≤ 2 ^ (-104 : ℤ) := by
    rw [pow_mul, h56]
    have := key _ _ (by norm_num) hR
    simpa only [Nat.cast_ofNat] using this
  rw [generationThreshold_def, show 9853 = 56 * 175 + 53 by norm_num, pow_add]
  calc θ ^ (56 * 175) * θ ^ 53 ≤ 2 ^ (-104 : ℤ) * 1 :=
        mul_le_mul h175 (pow_le_one₀ hθ0 hθ1) (by positivity) (by positivity)
    _ = 2 ^ (-104 : ℤ) := mul_one _

/-- `2^{-20} j^{5/2} θ^j ≤ 2^{-90} (199/200)^{j-N_*}` for `j ≥ N_*`. -/
private lemma cap_le_geometric {j : ℕ} (hj : generationThreshold ≤ j) :
    (2 : ℝ) ^ (-20 : ℝ) * (j : ℝ) ^ (5 / 2 : ℝ) *
        ((growthRatio : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ))) ^ (j : ℝ) ≤
      (2 : ℝ) ^ (-90 : ℤ) * (199 / 200 : ℝ) ^ (j - generationThreshold) := by
  set θ : ℝ := (growthRatio : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ)) with hθdef
  have hg := growthRatio_cast_pos
  have hθ : 0 < θ := by positivity
  rw [Real.rpow_natCast]
  have h20 : (2 : ℝ) ^ (-20 : ℝ) = 2 ^ (-20 : ℤ) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [h20]
  refine le_mul_pow_sub_of_succ_le (a := fun j : ℕ =>
    (2 : ℝ) ^ (-20 : ℤ) * (j : ℝ) ^ (5 / 2 : ℝ) * θ ^ j) (by norm_num) ?_ ?_ hj
  · have h1 := generationThreshold_rpow_lt_two_pow
    have h2 := capRatio_pow_generationThreshold_le
    rw [← hθdef] at h2
    have hq : 0 ≤ (generationThreshold : ℝ) ^ (5 / 2 : ℝ) := by positivity
    calc (2 : ℝ) ^ (-20 : ℤ) * (generationThreshold : ℝ) ^ (5 / 2 : ℝ) * θ ^ generationThreshold
        ≤ 2 ^ (-20 : ℤ) * 2 ^ 34 * 2 ^ (-104 : ℤ) := by gcongr
      _ = 2 ^ (-90 : ℤ) := by
          rw [← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
          norm_num
  · intro j hj
    have h := cap_ratio_real hj
    rw [← hθdef] at h
    change (2 : ℝ) ^ (-20 : ℤ) * ((j + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) * θ ^ (j + 1) ≤
      199 / 200 * ((2 : ℝ) ^ (-20 : ℤ) * (j : ℝ) ^ (5 / 2 : ℝ) * θ ^ j)
    have hp : 0 < (2 : ℝ) ^ (-20 : ℤ) * θ ^ j := by positivity
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h hp.le]

/-! ### The geometric bounds -/

/-- **Geometric bound for the propagation majorant.** For `j ≥ N_*`,
`E_j ≤ (7584/10^6) (990945/10^6)^{j-N_*} + 2^{-90} (199/200)^{j-N_*}`. -/
@[collatz_pos_dens "lem_ph_Ej_geometric"]
theorem propagationMajorant_le_geometric {j : ℕ} (hj : generationThreshold ≤ j) :
    propagationMajorant j ≤ 7584 / 10 ^ 6 * (990945 / 10 ^ 6 : ℝ) ^ (j - generationThreshold) +
      (2 : ℝ) ^ (-90 : ℤ) * (199 / 200 : ℝ) ^ (j - generationThreshold) := by
  have h := propagationMajorant_le_split j
  have ha := propagationMixingMajorant_le_geometric hj
  have hb := central_le_geometric hj
  have hc := cap_le_geometric hj
  linarith

/-- **Geometric bound for the central increments.** For an odd positive integer `t` and
`j ≥ N_*`,
`|Z_{j+1}(t) - Z_j(t)| ≤ (7584/10^6) (990945/10^6)^{j-N_*} + 2^{-90} (199/200)^{j-N_*}`. -/
theorem abs_weightedCentralSum_succ_sub_le_geometric {t : ℤ} (hodd : Odd t) (ht : 0 < t) {j : ℕ}
    (hj : generationThreshold ≤ j) :
    |weightedCentralSum (j + 1) t - weightedCentralSum j t| ≤
      7584 / 10 ^ 6 * (990945 / 10 ^ 6 : ℝ) ^ (j - generationThreshold) +
      (2 : ℝ) ^ (-90 : ℤ) * (199 / 200 : ℝ) ^ (j - generationThreshold) :=
  (abs_weightedCentralSum_succ_sub_le hodd ht hj).trans (propagationMajorant_le_geometric hj)

end CollatzPosDens
