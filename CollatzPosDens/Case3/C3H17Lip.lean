/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.StoppingTrace.TrLipConst

/-!
# Lipschitz constants of the future costs

For integers `h ≥ 1` the rationals `𝖫_h` are defined by downward recursion: `𝖫_h = 0` for
`h ≥ 15`, and for `1 ≤ h ≤ 14`
`𝖫_h = 2^{-h} ∑_{d=3}^{17-h} ϖ(d) ℓ_d 2^{-d} + 9 ∑_{2 ≤ d ≤ 15-h, d ∉ {4,5}} ϖ(d) 𝖫_{h+d}`,
where `ϖ` is the Pascal weight and `ℓ_d` the Lipschitz constants of the capped packet factors.
They are Lipschitz constants of the future costs `cf_h`.

## Main definitions

* `CollatzPosDens.c3H17Lip`: the rational constant `𝖫_h`.

## Main results

* `CollatzPosDens.c3H17Lip_of_le`: `𝖫_h = 0` for `h ≥ 15`.
* `CollatzPosDens.c3H17Lip_of_lt`: the recursion for `h < 15`, with rational Pascal weights.
* `CollatzPosDens.c3H17Lip_cast_of_lt`: the recursion read in `ℝ`, with the weights `ϖ(d)`.
* `CollatzPosDens.c3H17Lip_nonneg`: `0 ≤ 𝖫_h`.

## Implementation notes

The constant is computable and rational-valued. The Pascal weight `ϖ(d) = (d - 1) 2^{-d}` (for
`d ≥ 2`) is real-valued in `CollatzPosDens.varpi`, so the definition uses its rational form
`(d - 1) 2^{-d}` on the summation ranges, where `d ≥ 2`; `c3H17Lip_cast_of_lt` restates the
recursion with `varpi`. The index `h` ranges over all of `ℤ`, and for `h ≤ 0` the same recursion
is used.
-/

@[expose] public section

namespace CollatzPosDens

/-- The Lipschitz constants of the future costs: `𝖫_h = 0` for `h ≥ 15`, and otherwise
`𝖫_h = 2^{-h} ∑_{d=3}^{17-h} ϖ(d) ℓ_d 2^{-d} + 9 ∑_{2 ≤ d ≤ 15-h, d ∉ {4,5}} ϖ(d) 𝖫_{h+d}`,
with the Pascal weight written as `ϖ(d) = (d - 1) 2^{-d}`. -/
@[collatz_pos_dens "def_c3_h17_lip"]
def c3H17Lip (h : ℤ) : ℚ :=
  if 15 ≤ h then 0
  else
    (2 : ℚ) ^ (-h) * ∑ d ∈ Finset.Icc (3 : ℤ) (17 - h),
        ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) * trLipConst d * (2 : ℚ) ^ (-d) +
      9 * ∑ d ∈ ((Finset.Icc (2 : ℤ) (15 - h)).filter (· ∉ ({4, 5} : Finset ℤ))).attach,
        (((d : ℤ) : ℚ) - 1) * (2 : ℚ) ^ (-(d : ℤ)) * c3H17Lip (h + d)
termination_by (15 - h).toNat
decreasing_by
  have := d.2
  simp only [Finset.mem_filter, Finset.mem_Icc] at this
  omega

/-- The constant `𝖫_h` vanishes for `h ≥ 15`. -/
theorem c3H17Lip_of_le {h : ℤ} (hh : 15 ≤ h) : c3H17Lip h = 0 := by
  rw [c3H17Lip]
  simp [hh]

/-- The recursion defining `𝖫_h` for `h < 15`. -/
theorem c3H17Lip_of_lt {h : ℤ} (hh : h < 15) :
    c3H17Lip h =
      (2 : ℚ) ^ (-h) * ∑ d ∈ Finset.Icc (3 : ℤ) (17 - h),
          ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) * trLipConst d * (2 : ℚ) ^ (-d) +
        9 * ∑ d ∈ (Finset.Icc (2 : ℤ) (15 - h)).filter (· ∉ ({4, 5} : Finset ℤ)),
          ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) * c3H17Lip (h + d) := by
  rw [c3H17Lip, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    Finset.sum_attach _ (fun d : ℤ => ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) * c3H17Lip (h + d))]

/-- The rational Pascal weight agrees with `ϖ` for `d ≥ 2`. -/
private theorem cast_pascal {d : ℤ} (hd : 2 ≤ d) :
    ((((d : ℚ) - 1) * (2 : ℚ) ^ (-d) : ℚ) : ℝ) = varpi d := by
  rw [varpi_of_two_le hd]
  push_cast
  rfl

/-- The recursion for `𝖫_h`, `h < 15`, read in `ℝ` with the Pascal weights `ϖ(d)`. -/
theorem c3H17Lip_cast_of_lt {h : ℤ} (hh : h < 15) :
    (c3H17Lip h : ℝ) =
      (2 : ℝ) ^ (-h) * ∑ d ∈ Finset.Icc (3 : ℤ) (17 - h),
          varpi d * trLipConst d * (2 : ℝ) ^ (-d) +
        9 * ∑ d ∈ (Finset.Icc (2 : ℤ) (15 - h)).filter (· ∉ ({4, 5} : Finset ℤ)),
          varpi d * c3H17Lip (h + d) := by
  rw [c3H17Lip_of_lt hh]
  push_cast
  congr 2
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    rw [← cast_pascal (by omega)]
    push_cast
    ring
  · refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    rw [← cast_pascal (by omega)]
    push_cast
    ring

/-- The Lipschitz constants of the future costs are nonnegative. -/
theorem c3H17Lip_nonneg (h : ℤ) : 0 ≤ c3H17Lip h := by
  rcases le_or_gt 15 h with hh | hh
  · rw [c3H17Lip_of_le hh]
  rw [c3H17Lip_of_lt hh]
  refine add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun d hd => ?_))
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun d hd => ?_))
  · rw [Finset.mem_Icc] at hd
    have : (0 : ℚ) ≤ (d : ℚ) - 1 := by
      have : (3 : ℚ) ≤ d := by exact_mod_cast hd.1
      linarith
    have := trLipConst_nonneg d
    positivity
  · simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    have : (0 : ℚ) ≤ (d : ℚ) - 1 := by
      have : (2 : ℚ) ≤ d := by exact_mod_cast hd.1.1
      linarith
    have := c3H17Lip_nonneg (h + d)
    positivity
termination_by (15 - h).toNat
decreasing_by
  simp only [Finset.mem_filter, Finset.mem_Icc] at *
  omega

end CollatzPosDens
