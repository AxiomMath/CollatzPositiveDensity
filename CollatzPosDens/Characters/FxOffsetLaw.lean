/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RefDensityDecomp

/-!
# The offset law of the reference law

For every `n ∈ ℕ` and `y ∈ G_n`,
`μ_n(y) = ∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} [[off(w)]_n = y]`, an identity in `[0, ∞]`: the reference
law `μ_n` is the pushforward of the geometric weights `2^{-A(w)}` on words of length `n` along
`w ↦ [off(w)]_n`.

The proof applies `CollatzPosDens.ofReal_refDensity_eq_tsum_transfer` with `d = Q = n`. On the
one-point space `G_0` the density is `ρ_0 = 2/3`, the residue map is `φ_w(0) = [off(w)]_n`, and
`ω(w) = 3^n 2^{-A(w)}`, so `(𝒯_w ρ_0)(y) = (2/3) 3^n 2^{-A(w)} [[off(w)]_n = y]`. Comparing with
`ρ_n(y) = (2/3) 3^n μ_n(y)` and cancelling the finite positive factor `(2/3) 3^n` gives the law.

## Main results

* `CollatzPosDens.refLaw_eq_tsum_off`: `μ_n(y) = ∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} [[off(w)]_n = y]`.

## Implementation notes

The set `ℤ_{≥1}^n` is the set of words of length `n`, and the Iverson bracket
`2^{-A(w)} [P]` is written `if P then 2^{-A(w)} else 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The transfer of `ρ_0` along a word, read in `[0, ∞]`:
`(𝒯_w ρ_0)(y) = (2/3) 3^{|w|} 2^{-A(w)} [[off(w)]_{|w|} = y]`. Here `y ∈ G_{|w|}` is read in
`G_{t + |w|}` for any `t = 0`. -/
private theorem ofReal_transfer_refDensity_zero (w : Word) {t : ℕ} (ht : t = 0)
    (h : ResidueGroup w.length = ResidueGroup (t + w.length)) (y : ResidueGroup w.length) :
    ENNReal.ofReal (transfer w (refDensity t) (cast h y)) =
      2 / 3 * 3 ^ w.length *
        if dyadicRed w.length ⟨off w, off_mem_dyadicRationals w⟩ = y then
          (2 ^ w.valSum)⁻¹ else 0 := by
  subst ht
  have huniv : (univ : Finset (ResidueGroup 0)) = {0} := by decide
  have hmap : residueMap w 0 0 = dyadicRed (0 + w.length) ⟨off w, off_mem_dyadicRationals w⟩ := by
    simp [residueMap_apply]
  have hcast : ∀ (m : ℕ) (hm : w.length = m) (h : ResidueGroup w.length = ResidueGroup m),
      (dyadicRed m ⟨off w, off_mem_dyadicRationals w⟩ = cast h y ↔
        dyadicRed w.length ⟨off w, off_mem_dyadicRationals w⟩ = y) := by
    rintro m rfl h
    rfl
  rw [ofReal_transfer _ (fun z => refDensity_nonneg 0 z), huniv, filter_singleton, hmap]
  simp only [hcast _ (Nat.zero_add _).symm h, ← refLaw_mul_eq_ofReal_refDensity]
  have hw : ENNReal.ofReal (w.weight : ℝ) = 3 ^ w.length * (2 ^ w.valSum)⁻¹ := by
    rw [Word.weight, Rat.cast_div, Rat.cast_pow, Rat.cast_pow, ENNReal.ofReal_div_of_pos
      (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num),
      ENNReal.div_eq_inv_mul]
    norm_num
    ring
  split_ifs <;> simp [hw]
  ring

/-- **Offset law of the reference law.** For every `n ∈ ℕ` and `y ∈ G_n`,
`μ_n(y) = ∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} [[off(w)]_n = y]` in `[0, ∞]`. -/
@[collatz_pos_dens "lem_fx_offset_law"]
theorem refLaw_eq_tsum_off (n : ℕ) (y : ResidueGroup n) :
    refLaw n y = ∑' w : {w : Word | w.length = n},
      if dyadicRed n ⟨off w.1, off_mem_dyadicRationals w.1⟩ = y then
        (2 ^ w.1.valSum)⁻¹ else 0 := by
  have hc0 : (2 / 3 * 3 ^ n : ℝ≥0∞) ≠ 0 := by simp
  have hct : (2 / 3 * 3 ^ n : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by simp)) (by simp)
  refine (ENNReal.mul_right_inj hc0 hct).1 ?_
  rw [refLaw_mul_eq_ofReal_refDensity, ofReal_refDensity_eq_tsum_transfer le_rfl,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun ⟨w, hw⟩ => ?_
  subst hw
  exact ofReal_transfer_refDensity_zero w (Nat.sub_self _) _ y

end CollatzPosDens
