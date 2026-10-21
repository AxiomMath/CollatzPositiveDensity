/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPacketFn
public import CollatzPosDens.BlackSet.BkTheta

/-!
# The raw factor

Fix `n : ℕ` and a frequency `ξ ∈ G_n`. For a point `p ∈ 𝒫` and an integer `c`, the *raw factor*
is `φ_c(p) = Φ_{c-1}(ϑ_{n,ξ}(p))` when `c ≥ 2`, and `φ_c(p) = 1` when `c ≤ 1`, where `Φ_t` is the
packet function and `ϑ_{n,ξ}(p)` the angle of `p`. Since `0 ≤ Φ_t ≤ 1`, the raw factor lies in
`[0, 1]`.

## Main definitions

* `CollatzPosDens.chRawFactor n ξ c p`: the raw factor `φ_c(p)`.

## Main results

* `CollatzPosDens.chRawFactor_of_two_le`, `CollatzPosDens.chRawFactor_of_le_one`:
  the two cases of the definition.
* `CollatzPosDens.chRawFactor_nonneg`, `CollatzPosDens.chRawFactor_le_one`:
  `0 ≤ φ_c(p) ≤ 1`.

## Implementation notes

The packet length `c - 1` is passed to `chPacketFn` as the natural number `(c - 1).toNat`, which
equals `c - 1` when `c ≥ 2`. The factor is defined for every `p : ℤ × ℤ`, not only for
`p ∈ 𝒫`, since the angle `bkTheta` is.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The raw factor `φ_c(p)`: equal to `Φ_{c-1}(ϑ_{n,ξ}(p))` if `c ≥ 2`, and to `1` otherwise. -/
@[collatz_pos_dens "def_ch_raw_factor"]
noncomputable def chRawFactor (n : ℕ) (ξ : ResidueGroup n) (c : ℤ) (p : ℤ × ℤ) : ℝ :=
  if 2 ≤ c then chPacketFn (c - 1).toNat (bkTheta n ξ p) else 1

/-- The raw factor for `c ≥ 2`. -/
theorem chRawFactor_of_two_le (n : ℕ) (ξ : ResidueGroup n) {c : ℤ} (hc : 2 ≤ c)
    (p : ℤ × ℤ) : chRawFactor n ξ c p = chPacketFn (c - 1).toNat (bkTheta n ξ p) := by
  simp [chRawFactor, hc]

/-- The raw factor for `c ≥ 2`, with the packet length written as `m` where `c = m + 1`. -/
theorem chRawFactor_natCast_add_one (n : ℕ) (ξ : ResidueGroup n) {m : ℕ} (hm : 1 ≤ m)
    (p : ℤ × ℤ) : chRawFactor n ξ ((m : ℤ) + 1) p = chPacketFn m (bkTheta n ξ p) := by
  rw [chRawFactor_of_two_le n ξ (by omega)]
  congr 1
  omega

/-- The raw factor for `c ≤ 1` is `1`. -/
theorem chRawFactor_of_le_one (n : ℕ) (ξ : ResidueGroup n) {c : ℤ} (hc : c ≤ 1)
    (p : ℤ × ℤ) : chRawFactor n ξ c p = 1 := by
  simp [chRawFactor, show ¬ 2 ≤ c by omega]

/-- The raw factor is nonnegative. -/
theorem chRawFactor_nonneg (n : ℕ) (ξ : ResidueGroup n) (c : ℤ) (p : ℤ × ℤ) :
    0 ≤ chRawFactor n ξ c p := by
  unfold chRawFactor
  split_ifs
  · exact chPacketFn_nonneg _ _
  · exact zero_le_one

/-- The raw factor is at most `1`. -/
theorem chRawFactor_le_one (n : ℕ) (ξ : ResidueGroup n) (c : ℤ) (p : ℤ × ℤ) :
    chRawFactor n ξ c p ≤ 1 := by
  unfold chRawFactor
  split_ifs
  · exact chPacketFn_le_one _ _
  · exact le_rfl

end CollatzPosDens
