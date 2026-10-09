/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.FourierDecay.ChFifthMoment
public import Mathlib.Analysis.MeanInequalities

/-!
# Real moments of the geometric law `ν₄₅`

For every real `A` with `0 < A ≤ 5`, the series `∑_{j ≥ 1} ν₄₅(j) j^A` converges and its sum is
at most `20^A`.

Put `θ = A / 5 ∈ (0, 1]`. The weighted arithmetic–geometric mean inequality gives, for `x ≥ 0`,
`(x / 20⁵)^θ ≤ θ x / 20⁵ + (1 - θ)`, i.e. `x^θ` lies below the tangent line of the concave
function `t ↦ t^θ` at `20⁵`. Applying this at `x = j⁵` and summing against `ν₄₅`, using
`∑ ν₄₅ = 1` and `∑ ν₄₅(j) j⁵ ≤ 20⁵`, gives `∑ ν₄₅(j) j^A ≤ 20^A (θ + 1 - θ) = 20^A`.

## Main results

* `CollatzPosDens.nu45_rpow_moment_le`: for `0 < A ≤ 5` the series `∑_j ν₄₅(j) j^A` over
  `j ∈ ℤ` is summable with sum at most `20^A`.

## Implementation notes

The tangent line is taken directly at `20⁵` rather than at the fifth moment `M`, which needs no
lower bound on `M`. As in `nu45_fifth_moment_le`, the sum is taken over all of `ℤ`, the domain
of `nu45`; the terms with `j ≤ 0` vanish since `ν₄₅(j) = 0` there, so this is the sum over
`j ≥ 1`. The power `j^A` is the real power `Real.rpow`, and summability is recorded explicitly.
-/

@[expose] public section

namespace CollatzPosDens

/-- Pointwise tangent-line bound: for `0 < A ≤ 5` and every `j ∈ ℤ`,
`ν₄₅(j) j^A ≤ 20^A (θ ν₄₅(j) j⁵ / 20⁵ + (1 - θ) ν₄₅(j))` with `θ = A / 5`. -/
private lemma nu45_rpow_moment_le_aux {A : ℝ} (hA : 0 < A) (hA5 : A ≤ 5) (j : ℤ) :
    0 ≤ nu45 j * (j : ℝ) ^ A ∧
      nu45 j * (j : ℝ) ^ A ≤
        (20 : ℝ) ^ A * (A / 5 / 20 ^ 5 * (nu45 j * (j : ℝ) ^ 5) + (1 - A / 5) * nu45 j) := by
  rcases le_or_gt j 0 with hj | hj
  · simp [nu45_of_nonpos hj]
  have hj0 : (0 : ℝ) ≤ j := by exact_mod_cast hj.le
  have hθ0 : 0 ≤ A / 5 := by positivity
  have hθ1 : 0 ≤ 1 - A / 5 := by linarith
  have hx : (0 : ℝ) ≤ (j : ℝ) ^ 5 / 20 ^ 5 := by positivity
  have key := Real.geom_mean_le_arith_mean2_weighted hθ0 hθ1 hx zero_le_one (by ring)
  rw [Real.one_rpow, mul_one, Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hj0, ← Real.rpow_mul (by norm_num)]
    at key
  push_cast at key
  rw [show (5 : ℝ) * (A / 5) = A by ring, mul_one,
    show (j : ℝ) ^ (5 : ℝ) = (j : ℝ) ^ (5 : ℕ) by exact_mod_cast Real.rpow_natCast (j : ℝ) 5]
    at key
  rw [div_le_iff₀ (by positivity)] at key
  have hν := nu45_nonneg j
  refine ⟨mul_nonneg hν (Real.rpow_nonneg hj0 _), ?_⟩
  calc nu45 j * (j : ℝ) ^ A ≤ nu45 j * ((A / 5 * ((j : ℝ) ^ 5 / 20 ^ 5) + (1 - A / 5)) * 20 ^ A) :=
        mul_le_mul_of_nonneg_left key hν
    _ = _ := by ring

/-- **Real moments of the horizontal hold law.** For every real `A` with `0 < A ≤ 5`, the series
`∑_j ν₄₅(j) j^A` over `j ∈ ℤ` (whose nonzero terms are those with `j ≥ 1`) converges and its sum
is at most `20^A`. -/
@[collatz_pos_dens "lem_ch_real_moment"]
theorem nu45_rpow_moment_le {A : ℝ} (hA : 0 < A) (hA5 : A ≤ 5) :
    Summable (fun j : ℤ ↦ nu45 j * (j : ℝ) ^ A) ∧ ∑' j : ℤ, nu45 j * (j : ℝ) ^ A ≤ 20 ^ A := by
  obtain ⟨hs5, hle5⟩ := nu45_fifth_moment_le
  have hg : HasSum (fun j : ℤ ↦
      (20 : ℝ) ^ A * (A / 5 / 20 ^ 5 * (nu45 j * (j : ℝ) ^ 5) + (1 - A / 5) * nu45 j))
      ((20 : ℝ) ^ A * (A / 5 / 20 ^ 5 * ∑' j : ℤ, nu45 j * (j : ℝ) ^ 5 + (1 - A / 5) * 1)) :=
    ((hs5.hasSum.mul_left _).add (hasSum_nu45.mul_left _)).mul_left _
  have hs : Summable (fun j : ℤ ↦ nu45 j * (j : ℝ) ^ A) :=
    hg.summable.of_nonneg_of_le (fun j ↦ (nu45_rpow_moment_le_aux hA hA5 j).1)
      (fun j ↦ (nu45_rpow_moment_le_aux hA hA5 j).2)
  refine ⟨hs, (hasSum_le (fun j ↦ (nu45_rpow_moment_le_aux hA hA5 j).2) hs.hasSum hg).trans ?_⟩
  have h20 : (0 : ℝ) < 20 ^ A := by positivity
  have : A / 5 / 20 ^ 5 * ∑' j : ℤ, nu45 j * (j : ℝ) ^ 5 ≤ A / 5 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_left hle5 (by positivity)
  nlinarith

end CollatzPosDens
