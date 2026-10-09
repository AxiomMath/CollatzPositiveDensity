/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChDist
public import CollatzPosDens.CharSum.ChQmDominate
public import CollatzPosDens.FourierDecay.ChQmThreshold

/-!
# A pointwise bound on `Q`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. Let `A ≥ 1` be real and `D ≥ 1` an
integer, and suppose that `Q_m ≤ Q_{m-1}` for every integer `m` with `D ≤ m ≤ ⌊n/2⌋`. Then
`Q(p) ≤ D^A d_J(p)^{-A}` for every `p ∈ 𝒫`. Indeed every `p ∈ 𝒫` has
`j(p) ≥ 1 ≥ 0 = ⌊n/2⌋ ∸ ⌊n/2⌋`, so `d_J(p)^A Q(p) ≤ Q_{⌊n/2⌋} ≤ D^A`, and `d_J(p)^A > 0`.

## Main results

* `CollatzPosDens.chQ_le_threshold_rpow_mul`: `Q(p) ≤ D^A d_J(p)^{-A}` for all `p ∈ 𝒫`.
* `CollatzPosDens.chQ_le_threshold_rpow_mul_div`: the same bound written as
  `Q(p) ≤ D^A / d_J(p)^A`.

## Implementation notes

The exponent `A` is only required to satisfy `0 ≤ A` rather than `A ≥ 1`; powers are the real
power `Real.rpow`, as in `CollatzPosDens.chQm`. The threshold `ε` is arbitrary.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The pointwise bound in quotient form: if `D ≥ 1` and `Q_m ≤ Q_{m-1}` for every `m` with
`D ≤ m ≤ ⌊n/2⌋`, then `Q(p) ≤ D^A / d_J(p)^A` for every `p ∈ 𝒫`. -/
theorem chQ_le_threshold_rpow_mul_div (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ}
    (hA : 0 ≤ A) {D : ℕ} (hD : 1 ≤ D)
    (hmono : ∀ m, D ≤ m → m ≤ n / 2 → chQm n ξ ε A m ≤ chQm n ξ ε A (m - 1))
    {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    chQ n ξ ε p ≤ (D : ℝ) ^ A / (chDist n p : ℝ) ^ A := by
  have hpos : (0 : ℝ) < (chDist n p : ℝ) ^ A := by
    have := chDist_pos n p
    positivity
  rw [le_div_iff₀ hpos, mul_comm]
  have hj : ((n / 2 - n / 2 : ℕ) : ℤ) ≤ bkJ p := by
    rw [mem_bkPoints] at hp
    omega
  exact (chQm_dominate n ξ ε hA (n / 2) hp hj).trans
    (chQm_le_threshold_pow n ξ ε hA hD hmono (n / 2) le_rfl)

/-- **Pointwise bound on `Q`.** If `D ≥ 1` and `Q_m ≤ Q_{m-1}` for every `m` with
`D ≤ m ≤ ⌊n/2⌋`, then `Q(p) ≤ D^A d_J(p)^{-A}` for every `p ∈ 𝒫`. -/
@[collatz_pos_dens "lem_ch_Q_pointwise"]
theorem chQ_le_threshold_rpow_mul (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ}
    (hA : 0 ≤ A) {D : ℕ} (hD : 1 ≤ D)
    (hmono : ∀ m, D ≤ m → m ≤ n / 2 → chQm n ξ ε A m ≤ chQm n ξ ε A (m - 1))
    {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    chQ n ξ ε p ≤ (D : ℝ) ^ A * (chDist n p : ℝ) ^ (-A) := by
  rw [Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv]
  exact chQ_le_threshold_rpow_mul_div n ξ ε hA hD hmono hp

end CollatzPosDens
