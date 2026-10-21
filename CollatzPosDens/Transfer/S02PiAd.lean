/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Eta
public import CollatzPosDens.Transfer.S02Qpack
public import CollatzPosDens.Transfer.S02Ci
public import CollatzPosDens.Transfer.S02Hpack
public import CollatzPosDens.Transfer.S02GammaPk
public import CollatzPosDens.Transfer.S02Ai
public import CollatzPosDens.Transfer.S02AiPos
public import CollatzPosDens.Transfer.S02ScheduleValues
public import CollatzPosDens.Transfer.S02PiAdPlus
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The adaptive packing sum `Π_ad(ι)`

For a Fourier index `ι ∈ 𝔍 = {o, b}`, the adaptive packing sum is the rational number
$$\Pi_{\mathrm{ad}}(\iota) := \sum_{i=0}^{r_*(\iota)-1} \eta_i(\iota)\,
  \frac{\mathsf q_{\mathrm{pack}}\mathsf C_i(\iota)
    + \frac{127}{40}\bigl(H_{\mathrm{pk}}(\iota)\mathsf q_{\mathrm{pack}}
      + \Gamma_{\mathrm{pk}}/4\bigr)}{\mathsf A_i(\iota)},$$
where `η_i(ι)` are the event coefficients (`η_i(o) = θ^en_i = (77/100)^i` and
`(η_0(b), η_1(b), η_2(b)) = (1, 77/100, b_*)` with `b_* = 333407/10⁶`), `q_pack` the packing ratio,
`C_i(ι)` the packing numerators, `H_pk(ι)` the packing height, `Γ_pk` the packing offset and
`A_i(ι)` the adaptive denominators of the trace schedule. It is a sum of `r_*(ι)` explicit positive
rationals (ten for `o`, three for `b`): `Π_ad(o) = 0.0117855141445246195…` and
`Π_ad(b) = 0.0172936863842031617…`, bounded above by their roundings
`Π⁺_ad(o) = 0.0117855141445251` and `Π⁺_ad(b) = 0.0172936863842033`.

## Main definitions

* `CollatzPosDens.piAd`: the adaptive packing sum `Π_ad(ι) ∈ ℚ`.

## Main results

* `CollatzPosDens.piAd_pos`: `0 < Π_ad(ι)`.
* `CollatzPosDens.piAd_le_piAdPlus`: `Π_ad(ι) ≤ Π⁺_ad(ι)`.

## Implementation notes

The bound `Π_ad(ι) ≤ Π⁺_ad(ι)` is proved by exact rational evaluation, separately at each
index: the schedule positions are read off from `CollatzPosDens.schedule_values_o` and
`CollatzPosDens.schedule_values_b`, the size factors `K_{*,i}(ι)` from their definition and the
event coefficients from `CollatzPosDens.eventCoeff_o_eq` and `CollatzPosDens.eventCoeff_b_zero`,
`CollatzPosDens.eventCoeff_b_one`, `CollatzPosDens.eventCoeff_b_two`, after which each summand is
an explicit rational.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The adaptive packing sum
`Π_ad(ι) := ∑_{i < r_*(ι)} η_i(ι) (q_pack C_i(ι) + 127/40 (H_pk(ι) q_pack + Γ_pk / 4)) / A_i(ι)`.
-/
@[collatz_pos_dens "def_s02_Pi_ad"]
def piAd (ι : FIndex) : ℚ :=
  ∑ i ∈ range (rStar ι),
    eventCoeff ι i * (qPack * cStar ι i + 127 / 40 * (Hpack ι * qPack + Gammapk / 4)) /
      aStar ι i

/-- The defining formula of the adaptive packing sum. -/
theorem piAd_def (ι : FIndex) : piAd ι = ∑ i ∈ range (rStar ι),
    eventCoeff ι i * (qPack * cStar ι i + 127 / 40 * (Hpack ι * qPack + Gammapk / 4)) /
      aStar ι i :=
  rfl

/-- The adaptive packing sum is positive. -/
theorem piAd_pos (ι : FIndex) : 0 < piAd ι := by
  rw [piAd_def]
  apply sum_pos _ (nonempty_range_iff.2 (rStar_pos ι).ne')
  intro i _
  have := eventCoeff_pos ι i
  have := qPack_pos
  have := cStar_pos ι i
  have := Gammapk_pos
  have := aStar_pos ι i
  positivity

/-- The adaptive packing sum at the original index is at most its rounding. -/
theorem piAd_o_le_piAdPlus_o : piAd .o ≤ piAdPlus .o := by
  have h := schedule_values_o
  simp only [rStar_o, List.ofFn_succ, List.ofFn_zero, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h
  simp only [Fin.val_zero, Fin.val_succ, Fin.isValue] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [piAd_def, rStar_o, piAdPlus_o]
  simp only [sum_range_succ, sum_range_zero, eventCoeff_o_eq, cStar_apply_o, aStar_apply_o,
    sStar_cast, bAn_eq, qPack_eq, Hpack_cast_o, Gammapk_eq, Kstar_o_zero, Kstar_o_one,
    Kstar_o_two, Kstar_o_three, Kstar_o_four, Kstar_o_five, Kstar_o_six, Kstar_o_seven,
    Kstar_o_eight, Kstar_o_of_nine_le le_rfl]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num

/-- The adaptive packing sum at the bootstrap index is at most its rounding. -/
theorem piAd_b_le_piAdPlus_b : piAd .b ≤ piAdPlus .b := by
  have h := schedule_values_b
  simp only [rStar_b, List.ofFn_succ, List.ofFn_zero, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, -, -⟩ := h
  simp only [Fin.val_zero, Fin.val_succ, Fin.isValue] at h0 h1 h2
  rw [piAd_def, rStar_b, piAdPlus_b]
  simp only [sum_range_succ, sum_range_zero, eventCoeff_b_zero, eventCoeff_b_one,
    eventCoeff_b_two, stageRate_eq, cStar_apply_b, aStar_apply_b, sStar_cast, bAn_eq, qPack_eq,
    Hpack_cast_b, Gammapk_eq, Kstar_b_zero, Kstar_b_one, Kstar_b_two]
  rw [h0, h1, h2]
  norm_num

/-- The adaptive packing sum is at most its rounding: `Π_ad(ι) ≤ Π⁺_ad(ι)`. -/
@[collatz_pos_dens "lem_s02_Pi_ad"]
theorem piAd_le_piAdPlus (ι : FIndex) : piAd ι ≤ piAdPlus ι := by
  cases ι
  · exact piAd_o_le_piAdPlus_o
  · exact piAd_b_le_piAdPlus_b

end CollatzPosDens
