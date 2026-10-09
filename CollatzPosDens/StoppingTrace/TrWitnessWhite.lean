/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkExitRoom
public import CollatzPosDens.BlackSet.BkExitWhite
public import CollatzPosDens.BlackSet.BkSourceMem

/-!
# Exit witnesses of a black point are white

Let `ξ ∈ G_n` be a unit, and colour points at the scale `ε_*`. Let `v` be black with gap
`s = gap(v)`, and let `r, O` be integers with `0 ≤ r ≤ ⌊(5s + 16)/16⌋` and `1 ≤ O ≤ 4`. Then the
point `v + (r, s + O)` is white.

The canonical triangle `Δ = Δ(v)` lies in the family `𝔗`, and `v ∈ Δ` since `0 < ε_* < 1/27`.
Its top row is `l_Δ = l_*(v) = l(v) + s`. By `three_mul_epsStar_mul_nine_pow_lt_two_pow`,
`3 ε_* 9^r ≤ 3 ε_* 9^{⌊(5s+16)/16⌋} < 2^s`, so `isBkWhite_exit_of_mem_bkFamily` applied at
`u = v` shows that `(j(v) + r, l_Δ + O) = v + (r, s + O)` is white.

## Main results

* `CollatzPosDens.isBkWhite_add_of_bkBlack_trGap`: the point `v + (r, gap(v) + O)` is white.

## Implementation notes

Blackness is defined on the point set `𝒫`, so membership `v ∈ 𝒫` is a hypothesis. No assumption
`n ≥ 1` is needed, and the range of `r` includes `r = 0`. The floor `⌊(5s+16)/16⌋` of a
nonnegative rational with natural numerator is the natural-number division `(5 * s + 16) / 16`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Exit witnesses of a black point are white.** Let `ξ` be a unit, `v ∈ 𝒫` black at the
colour scale `ε_*`, `s = gap(v)`, and `r, O` integers with `0 ≤ r ≤ ⌊(5s+16)/16⌋` and
`1 ≤ O ≤ 4`. Then `v + (r, s + O)` is white. -/
@[collatz_pos_dens "lem_tr_witness_white"]
theorem isBkWhite_add_of_bkBlack_trGap {n : ℕ} {ξ : ResidueGroup n} {v : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v) {r O : ℤ}
    (hr₀ : 0 ≤ r) (hr : r ≤ (((5 * trGap n ξ (epsStar : ℝ) v + 16) / 16 : ℕ) : ℤ))
    (hO₁ : 1 ≤ O) (hO₄ : O ≤ 4) :
    IsBkWhite n ξ (epsStar : ℝ) (v + (r, (trGap n ξ (epsStar : ℝ) v : ℤ) + O)) := by
  set s := trGap n ξ (epsStar : ℝ) v with hs
  obtain ⟨hε, hε'⟩ := epsStar_mem_bkRange (K := ℝ)
  have hΔ := bkCanonTriangle_mem_bkFamily hv hb
  have hu := mem_bkCanonTriangle_self hξ hε hε' hv hb
  have htop : bkL v + s = (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l := by
    rw [bkCanonTriangle_l, bkColTop_eq_add_trGap]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = m := ⟨r.toNat, by omega⟩
  have hm : m ≤ (5 * s + 16) / 16 := by exact_mod_cast hr
  have hroom : 3 * (epsStar : ℝ) * 9 ^ m < 2 ^ s := by
    refine lt_of_le_of_lt ?_ (three_mul_epsStar_mul_nine_pow_lt_two_pow (K := ℝ) s)
    gcongr
    norm_num
  have h := isBkWhite_exit_of_mem_bkFamily hξ hε hε' hΔ hu htop hroom hO₁ hO₄
  rw [← htop] at h
  convert h using 1
  obtain ⟨x, y⟩ := v
  simp only [bkJ, bkL, Prod.mk_add_mk]
  ring_nf

end CollatzPosDens
