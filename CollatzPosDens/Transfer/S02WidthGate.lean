/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Ai
public import CollatzPosDens.Transfer.S02Bi
public import CollatzPosDens.Transfer.S02Hpack

/-!
# The packing widths fit the adaptive denominators

For every Fourier index `ι` and every `0 ≤ i < r_*(ι)`, the packing width `B_i(ι)` together
with the packing expansion length `H_pk(ι)` fits in five sixteenths of the adaptive denominator:
$$\mathsf B_i(\iota) + H_{\mathrm{pk}}(\iota) \le \tfrac{5}{16}\,\mathsf A_i(\iota) .$$
Explicitly `B_i(o) + H_pk(o) = 21026/25 + (427481/100000) p_i(o)` and
`B_i(b) + H_pk(b) = 16798/25 + (107707/25000) p_i(b)`; on the schedule range the smallest
differences `(5/16) A_i(ι) - B_i(ι) - H_pk(ι)` are those at `i = 0`, equal to `402664.893…` for
`ι = o` and `52507.324…` for `ι = b` (the three differences at `ι = b` are `52507.324…`,
`1739417.864…`, `233053634.179…`); the largest ratio `(B_i + H_pk)/A_i` is `0.01047…` (at `i = 8`)
for `ι = o` and `0.01165…` (at `i = 1`) for `ι = b`.

## Main results

* `CollatzPosDens.packWidth_add_Hpack_le`: `B_i(ι) + H_pk(ι) ≤ (5/16) A_i(ι)` for every `ι` and
  every `i`, in particular for every `0 ≤ i < r_*(ι)`.

## Implementation notes

The thirteen cases on the schedule range are not evaluated one by one. Since
`S_i(ι) = K_{*,i}(ι) (p_i(ι) + 1)` with `K_{*,i}(ι) ≥ 268`, and `b_an > 1`, one has
`b_an S_i(ι) ≥ 268 (p_i(ι) + 1)`; this lower bound on `A_i(ι)` makes `(5/16) A_i(ι)` exceed
`B_i(ι) + H_pk(ι)` as soon as `p_i(ι) ≥ 20`, and every schedule position satisfies
`p_i(ι) ≥ p_init(ι) ≥ 169`. The bound therefore holds for every index `i : ℕ`, not only for
`i < r_*(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The packing widths fit: `B_i(ι) + H_pk(ι) ≤ (5/16) A_i(ι)` for every `ι` and every index
`i`, in particular for every `0 ≤ i < r_*(ι)`. -/
@[collatz_pos_dens "lem_s02_width_gate"]
theorem packWidth_add_Hpack_le (ι : FIndex) (i : ℕ) :
    packWidth ι i + Hpack ι ≤ 5 / 16 * aStar ι i := by
  have hK : (268 : ℚ) ≤ Kstar ι i := by exact_mod_cast le_Kstar ι i
  have hp : (pInit ι : ℚ) ≤ schedule ι i := by exact_mod_cast pInit_le_schedule ι i
  have hS : (268 : ℚ) * ((schedule ι i : ℚ) + 1) ≤ sStar ι i := by
    rw [sStar_cast]
    exact mul_le_mul_of_nonneg_right hK (by positivity)
  have hb : (1 : ℚ) < bAn := by rw [bAn_eq]; norm_num
  have hS0 : (0 : ℚ) ≤ sStar ι i := by positivity
  cases ι
  · rw [pInit_o, Nat.cast_ofNat] at hp
    rw [aStar_apply_o, packWidth_eq_o, Hpack_cast_o]
    nlinarith
  · rw [pInit_b, Nat.cast_ofNat] at hp
    rw [aStar_apply_b, packWidth_eq_b, Hpack_cast_b]
    nlinarith

/-- The packing widths fit on the schedule range: `B_i(ι) + H_pk(ι) ≤ (5/16) A_i(ι)` for
`0 ≤ i < r_*(ι)`. -/
theorem packWidth_add_Hpack_le_of_lt_rStar (ι : FIndex) {i : ℕ} (_hi : i < rStar ι) :
    packWidth ι i + Hpack ι ≤ 5 / 16 * aStar ι i :=
  packWidth_add_Hpack_le ι i

end CollatzPosDens
