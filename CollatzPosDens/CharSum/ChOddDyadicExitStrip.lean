/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkExitStrip
public import CollatzPosDens.BlackSet.BkExitWidthPow
public import CollatzPosDens.BlackSet.BkSourceMem

/-!
# Odd dyadic exits stay in the strip

Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black, and `ω ∈ ℕ` the vertical distance
`l_Δ - l(p)` from `p` to the top edge of its canonical triangle `Δ = Δ(p)`. For every
`0 ≤ r ≤ f_ω`, where `f_ω` is the exit width, the point `r` steps to the right of `p` still lies
in the strip: `j(p) + r ≤ ⌊n/2⌋`.

Indeed `9 ^ r ≤ 9 ^ f_ω ≤ 9 * 2 ^ ω`, so `3 ε 9 ^ r ≤ 27 ε 2 ^ ω < 2 ^ ω`; since `Δ(p)` belongs to
the canonical family and contains `p`, the exit-strip bound applies with `u = p` and `s = ω`.

## Main results

* `CollatzPosDens.bkJ_add_le_of_le_bkExitWidth`: `j(p) + r ≤ ⌊n/2⌋` for `r ≤ f_ω`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Odd dyadic exits stay in the strip.** Let `ξ` be a unit, `0 < ε < 1/27`, `p ∈ 𝒫` black,
`ω ∈ ℕ` with `l(p) + ω = l_{Δ(p)}`, and `r ∈ ℕ` with `r ≤ f_ω`. Then `j(p) + r ≤ ⌊n/2⌋`. -/
@[collatz_pos_dens "lem_ch_odd_dyadic_exit_strip"]
theorem bkJ_add_le_of_le_bkExitWidth {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {p : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hp : p ∈ bkPoints) (hb : BkBlack n ξ ε p) {ω : ℕ}
    (hω : bkL p + ω = (bkCanonTriangle n ξ ε p hp).l) {r : ℕ} (hr : r ≤ bkExitWidth ω) :
    bkJ p + r ≤ ((n / 2 : ℕ) : ℤ) := by
  have h9 : (9 : ℝ) ^ r ≤ 9 * 2 ^ ω := by
    have h := (Nat.pow_le_pow_right (by norm_num) hr).trans (nine_pow_bkExitWidth_le ω)
    exact_mod_cast h
  have h2 : (0 : ℝ) < 2 ^ ω := by positivity
  have hlt : 3 * ε * 9 ^ r < 2 ^ ω := by nlinarith
  exact bkJ_add_le_of_mem_bkFamily hξ hε₀ (bkCanonTriangle_mem_bkFamily hp hb)
    (mem_bkCanonTriangle_self hξ hε₀ hε hp hb) hω hlt

end CollatzPosDens
