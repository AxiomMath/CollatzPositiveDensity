/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02AiPos
public import CollatzPosDens.Transfer.S02WidthGate

/-!
# The thin-block packing ratios `ρ_i(ι)`

For a Fourier index `ι ∈ 𝔍 = {o, b}` and `0 ≤ i < r_*(ι)`, the `i`-th thin-block packing ratio is
the rational number
$$\rho_i(\iota) := \tfrac{127}{40}\,\bigl(\mathsf B_i(\iota) + H_{\mathrm{pk}}(\iota)\bigr)
  / \mathsf A_i(\iota),$$
where `B_i(ι)` is the packing width, `H_pk(ι)` the packing expansion length and `A_i(ι)` the
adaptive denominator of the trace schedule. It measures the relative excess of a thin block over
its width in the conditional packing of the square-root terms. Since `A_i(ι) > 0` and
`B_i(ι) + H_pk(ι) ≤ (5/16) A_i(ι)`, one has `0 < ρ_i(ι) ≤ 127/128 < 1`. On the schedule range the
values at `ι = b` are `ρ_0(b) = 0.02576…`, `ρ_1(b) = 0.03700…`, `ρ_2(b) = 0.00934…`.

## Main definitions

* `CollatzPosDens.thinPackRatio`: the ratio `ρ_i(ι) = (127/40)(B_i(ι) + H_pk(ι)) / A_i(ι) : ℚ`.

## Main results

* `CollatzPosDens.thinPackRatio_def`: the defining formula.
* `CollatzPosDens.thinPackRatio_pos`: `0 < ρ_i(ι)`.
* `CollatzPosDens.thinPackRatio_le`: `ρ_i(ι) ≤ 127/128`.
* `CollatzPosDens.thinPackRatio_lt_one`: `ρ_i(ι) < 1`.

## Implementation notes

The ratios are only meaningful for `0 ≤ i < r_*(ι)` (`CollatzPosDens.rStar`). The definition is
total on `ℕ`, since `B_i`, `H_pk` and `A_i` are, and the bounds above hold for every `i : ℕ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The thin-block packing ratios of the trace schedule:
`ρ_i(ι) := (127/40)(B_i(ι) + H_pk(ι)) / A_i(ι) ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_rho_pk"]
def thinPackRatio (ι : FIndex) (i : ℕ) : ℚ :=
  127 / 40 * (packWidth ι i + Hpack ι) / aStar ι i

/-- The defining formula `ρ_i(ι) = (127/40)(B_i(ι) + H_pk(ι)) / A_i(ι)`. -/
theorem thinPackRatio_def (ι : FIndex) (i : ℕ) :
    thinPackRatio ι i = 127 / 40 * (packWidth ι i + Hpack ι) / aStar ι i := rfl

/-- The thin-block packing ratios are positive. -/
theorem thinPackRatio_pos (ι : FIndex) (i : ℕ) : 0 < thinPackRatio ι i := by
  have := packWidth_pos ι i
  have := aStar_pos ι i
  rw [thinPackRatio_def]
  positivity

/-- The thin-block packing ratios are nonnegative. -/
theorem thinPackRatio_nonneg (ι : FIndex) (i : ℕ) : 0 ≤ thinPackRatio ι i :=
  (thinPackRatio_pos ι i).le

/-- The thin-block packing ratios are at most `127/128 = (127/40)(5/16)`. -/
theorem thinPackRatio_le (ι : FIndex) (i : ℕ) : thinPackRatio ι i ≤ 127 / 128 := by
  have hA := aStar_pos ι i
  have h := packWidth_add_Hpack_le ι i
  rw [thinPackRatio_def, div_le_iff₀ hA]
  linarith

/-- The thin-block packing ratios are below one. -/
theorem thinPackRatio_lt_one (ι : FIndex) (i : ℕ) : thinPackRatio ι i < 1 :=
  (thinPackRatio_le ι i).trans_lt (by norm_num)

end CollatzPosDens
