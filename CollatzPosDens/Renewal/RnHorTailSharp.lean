/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHorTail

/-!
# Sharp horizontal tail of the first-passage law

For `s ∈ ℕ` and real `u ≥ 2`, the mass of the first-passage law `F_s` on the columns `r` with
`|r - s/4| ≥ u` satisfies
$$\sum_{|r - s/4| \ge u}\ \sum_{\ell \in \mathbb{Z}} \mathsf F_s(r, \ell) \le
  \begin{cases} 4 e^{-u/256} & s \le 5, \\
    4 e^{-u^2/(2(s-4))} + 2 e^{-u/256} & s \ge 6. \end{cases}$$

For `s ≤ 5` every contributing column has `r ≥ 1`, which together with `u ≥ 2 > 5/4` forces
`r ≥ u`; the exponential moment `∑ F_s(r, ℓ) e^{r/16} ≤ M₄₅(1/16)^{s+1} ≤ (5/4)^6 ≤ 4` then gives
the bound `4 e^{-u/16}`. For `s ≥ 6` put `n = s - 4`; the exact crossing law bounds the column
mass by `e_n(r - 1) + ∑_j p_n(j) ν₄₅(r - 1 - j)`. Since `0 ≤ e_n ≤ p_n`, the tail is at most twice
the mass of the straddle weights `p_n(j)` with `|j - n/4| ≥ u/2`, plus the total straddle mass
`∑_j p_n(j) = 1` times the geometric tail `∑_{H ≥ u/2} ν₄₅(H)`. As `u ≥ 2`, both indices
`k ∈ {2j, 2j + 1}` of such a `j` satisfy `|k - n/2| ≥ u - 1 ≥ u/2`, so the Hoeffding bound for row
`n` makes the first mass at most `2 e^{-u²/(2n)}`.

## Main results

* `CollatzPosDens.tsum_firstPassageLaw_hor_tail_le_of_le_five`: the case `s ≤ 5`.
* `CollatzPosDens.tsum_firstPassageLaw_hor_tail_le_of_six_le`: the case `s ≥ 6`.

Summability of the column masses on `|r - s/4| ≥ u` is
`CollatzPosDens.summable_firstPassageLaw_hor_tail`.

## Implementation notes

The sum over `r` with `|r - s/4| ≥ u` is the unconditional sum over the subtype of such `r`. The
two cases follow from the bounds `CollatzPosDens.tsum_firstPassageLaw_hor_tail_le_four_mul_exp`
(`4 e^{-u/16}`) and `CollatzPosDens.tsum_firstPassageLaw_add_four_hor_tail_le`
(`4 e^{-u²/(2n)} + (5/4) e^{-u/32}`), using `e^{-u/16}, e^{-u/32} ≤ e^{-u/256}`. The geometric
tail of `ν₄₅` is bounded through the exponential moment `M₄₅(1/16) ≤ 5/4` rather than summed in
closed form: Markov's inequality gives `∑_{H ≥ u/2} ν₄₅(H) ≤ (5/4) e^{-u/32}`, which is at most
`2 e^{-u/256}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Sharp horizontal tail of the first-passage law, case `s ≤ 5`.** For `s ≤ 5` and real
`u ≥ 2`, `∑_{|r - s/4| ≥ u} ∑_{ℓ ∈ ℤ} F_s(r, ℓ) ≤ 4 exp(-u / 256)`. -/
@[collatz_pos_dens "lem_rn_hor_tail_sharp"]
theorem tsum_firstPassageLaw_hor_tail_le_of_le_five {s : ℕ} (hs : s ≤ 5) {u : ℝ} (hu : 2 ≤ u) :
    ∑' r : {r : ℤ // u ≤ |(r : ℝ) - s / 4|}, ∑' ℓ : ℤ, firstPassageLaw s ((r : ℤ), ℓ) ≤
      4 * exp (-(u / 256)) := by
  refine (tsum_firstPassageLaw_hor_tail_le_four_mul_exp hs hu).trans ?_
  gcongr
  linarith

/-- **Sharp horizontal tail of the first-passage law, case `s ≥ 6`.** For `s ≥ 6` and real
`u ≥ 2`, `∑_{|r - s/4| ≥ u} ∑_{ℓ ∈ ℤ} F_s(r, ℓ) ≤ 4 exp(-u² / (2 (s - 4))) + 2 exp(-u / 256)`. -/
@[collatz_pos_dens "lem_rn_hor_tail_sharp"]
theorem tsum_firstPassageLaw_hor_tail_le_of_six_le {s : ℕ} (hs : 6 ≤ s) {u : ℝ} (hu : 2 ≤ u) :
    ∑' r : {r : ℤ // u ≤ |(r : ℝ) - s / 4|}, ∑' ℓ : ℤ, firstPassageLaw s ((r : ℤ), ℓ) ≤
      4 * exp (-(u ^ 2 / (2 * ((s : ℝ) - 4)))) + 2 * exp (-(u / 256)) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 4 := ⟨s - 4, by omega⟩
  refine (tsum_firstPassageLaw_add_four_hor_tail_le (by omega) hu).trans ?_
  have h2 : exp (-(u / 32)) ≤ exp (-(u / 256)) := exp_le_exp.2 (by linarith)
  rw [show ((n + 4 : ℕ) : ℝ) - 4 = n by push_cast; ring]
  linarith [exp_pos (-(u / 256))]

end CollatzPosDens
