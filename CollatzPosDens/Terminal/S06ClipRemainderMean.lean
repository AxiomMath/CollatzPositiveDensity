/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06ClipRemainder
public import CollatzPosDens.Terminal.S06ClipDeficit
public import CollatzPosDens.Transfer.TransferAbsMean
public import CollatzPosDens.Mixing.Mixing
public import CollatzPosDens.Mixing.MxProfilePower

/-!
# Mean of the clipping remainder

For all integers `q ≥ 1` and `n ≥ mxGateLevel = 2^80`, and every real `B > 0`, the clipping
remainder `clipRemainder q n B` has mean
$$\langle \Phi^{\mathrm{clp}}_{q,n,B} \rangle_q ≤ 2 n^{-8} + \frac{2^{13}\sqrt{n \log n}}{B}
  + 2^{365} n^{-a_{\mathrm{mx}}(\mathrm o)} \log n.$$

If `q ≤ n` the remainder is `refDensity q - clipDensity q n B`, whose mean is bounded by
`residueAvg_refDensity_sub_clipDensity_le`, and the last term is nonnegative. If `q > n`, the
remainder is the pullback along `residueReduction` of `refDensity n - clipDensity n n B`, whose
mean is unchanged by the pullback, plus `|refDensity q - refDensity n ∘ residueReduction|`, whose
mean is bounded by `residueAvg_abs_refDensity_sub_le_of_two_pow_le` and
`mxProfile_o_le_two_pow_mul` by `2^365 n^{-a_mx(o)} log n`.

## Main results

* `CollatzPosDens.residueAvg_clipRemainder_le`: the mean bound above.

## Implementation notes

The power `n^{-8}` is written `((n : ℝ) ^ 8)⁻¹`, the power `n^{-a}` is the real power
`(n : ℝ) ^ (-(a : ℝ))`, and `log` is `Real.log`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Mean of the clipping remainder.** For all integers `q ≥ 1` and `n ≥ mxGateLevel` and every
real `B > 0`, `⟨Φ^clp_{q,n,B}⟩_q ≤ 2 n^{-8} + 2^13 √(n log n) / B + 2^365 n^{-a_mx(o)} log n`. -/
@[collatz_pos_dens "lem_s06_clip_remainder_mean"]
theorem residueAvg_clipRemainder_le {q n : ℕ} (hq : 1 ≤ q) (hn : mxGateLevel ≤ n) {B : ℝ}
    (hB : 0 < B) :
    residueAvg q (clipRemainder q n B) ≤
      2 * ((n : ℝ) ^ 8)⁻¹ + 2 ^ 13 * √(n * Real.log n) / B +
        2 ^ 365 * (n : ℝ) ^ (-(amix .o : ℝ)) * Real.log n := by
  have hn3 : 3 ≤ n := le_trans (by rw [mxGateLevel_def]; norm_num) hn
  have hnR : (mxGateLevel : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlast : 0 ≤ 2 ^ 365 * (n : ℝ) ^ (-(amix .o : ℝ)) * Real.log n := by
    have := Real.rpow_nonneg hn0.le (-(amix .o : ℝ))
    positivity
  have h3 := mxProfile_o_le_two_pow_mul hnR
  generalize 2 ^ 365 * (n : ℝ) ^ (-(amix .o : ℝ)) * Real.log n = M at hlast h3 ⊢
  by_cases hqn : q ≤ n
  · have e : clipRemainder q n B = fun y => refDensity q y - clipDensity q n B y :=
      funext fun y => clipRemainder_of_le hqn B y
    rw [e]
    linarith [residueAvg_refDensity_sub_clipDensity_le hq hqn hn3 hB]
  · have hnq : n ≤ q := (not_le.1 hqn).le
    have e : clipRemainder q n B =
        fun y => ((fun x => refDensity n x - clipDensity n n B x) ∘ residueReduction hnq) y +
          |refDensity q y - refDensity n (residueReduction hnq y)| :=
      funext fun y => clipRemainder_of_ge hnq B y
    rw [e, residueAvg_add, residueAvg_comp_residueReduction]
    have h1 := residueAvg_refDensity_sub_clipDensity_le (by omega) le_rfl hn3 hB
    have h2 := residueAvg_abs_refDensity_sub_le_of_two_pow_le .o hn hnq
    linarith

end CollatzPosDens
