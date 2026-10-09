/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Transfer

/-!
# Transfers vanish on nonunits

Let `w = (a₁, …, a_d)` be a word of length `d ≥ 1`, `t ∈ ℕ` and `g : G_t → ℝ`. Then the
transfer `𝒯_w g` vanishes at every nonunit `y ∈ G_{t+d}`.

Indeed, reduce the residue map `φ_w(z) = [3^d 2^{-A(w)}] z̃ + [off(w)]` modulo `3`: the first
term vanishes since `d ≥ 1`, and `off(w) = 2^{-a₁} (1 + 3 off(a₂, …, a_d))` reduces to
`2^{-a₁} ≢ 0 (mod 3)`. Hence every value of `φ_w` is a unit, a nonunit `y` has an empty fiber,
and `(𝒯_w g)(y)` is an empty sum.

## Main results

* `CollatzPosDens.isResidueUnit_residueMap`: for `|w| ≥ 1`, every value of `φ_w` is a unit.
* `CollatzPosDens.transfer_eq_zero_of_not_isResidueUnit`: for `|w| ≥ 1`, `(𝒯_w g)(y) = 0`
  for every nonunit `y`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For a nonempty word `w`, every value `φ_w(z)` of the residue map is a unit of
`G_{t+|w|}`: modulo `3` it reduces to `2^{-a₁} ≠ 0`. -/
theorem isResidueUnit_residueMap {w : Word} (hw : 0 < w.length) (t : ℕ)
    (z : ResidueGroup t) : IsResidueUnit (residueMap w t z) := by
  obtain ⟨a, w', rfl⟩ := List.exists_cons_of_length_pos hw
  set k := t + (a :: w').length
  have hdvd : 3 ∣ 3 ^ k := dvd_pow_self 3 (by simp [k])
  let f : dyadicRationals →+* ZMod 3 := (ZMod.castHom hdvd (ZMod 3)).comp (dyadicRed k)
  have hu : ((2 : ℚ) ^ (a : ℕ))⁻¹ ∈ dyadicRationals := by
    simpa using intCast_div_two_pow_mem 1 (a : ℕ)
  set u : dyadicRationals := ⟨_, hu⟩
  have hu2 : u * 2 ^ (a : ℕ) = 1 := Subtype.ext (by
    have h : ((2 : dyadicRationals) : ℚ) = 2 := rfl
    simp [u, h])
  have hfu : f u * 2 ^ (a : ℕ) = 1 := by
    have h := congrArg f hu2
    rwa [map_mul, map_pow, map_one, map_ofNat] at h
  have hoff : (⟨off (a :: w'), off_mem_dyadicRationals _⟩ : dyadicRationals) =
      u * (1 + 3 * ⟨off w', off_mem_dyadicRationals _⟩) :=
    Subtype.ext (by
      have h : ((3 : dyadicRationals) : ℚ) = 3 := rfl
      simp [u, h])
  have h3 : (3 : ZMod 3) = 0 := rfl
  have hfoff : f ⟨off (a :: w'), off_mem_dyadicRationals _⟩ = f u := by
    rw [hoff, map_mul, map_add, map_one, map_mul, map_ofNat, h3, zero_mul, add_zero, mul_one]
  have hfw : ZMod.castHom hdvd (ZMod 3)
      (dyadicRed k ⟨Word.weight (a :: w'), Word.weight_mem_dyadicRationals _⟩) = 0 := by
    rw [dyadicRed_weight, map_mul, map_pow, map_ofNat, h3, List.length_cons,
      zero_pow (Nat.succ_ne_zero _), zero_mul]
  have himage : ZMod.castHom hdvd (ZMod 3) (residueMap (a :: w') t z) = f u := by
    rw [residueMap_apply, map_add, map_mul, hfw, zero_mul, zero_add]
    exact hfoff
  intro hy
  have hzero : ZMod.castHom hdvd (ZMod 3) (residueMap (a :: w') t z) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, (ZMod.natCast_eq_zero_iff _ _).2 hy]
  rw [himage] at hzero
  rw [hzero, zero_mul] at hfu
  exact zero_ne_one hfu

/-- **Transfers vanish on nonunits.** For a word `w` of length `d ≥ 1`, `t ∈ ℕ` and
`g : G_t → ℝ`, `(𝒯_w g)(y) = 0` for every nonunit `y ∈ G_{t+d}`. -/
@[collatz_pos_dens "lem_transfer_nonunit"]
theorem transfer_eq_zero_of_not_isResidueUnit {w : Word} (hw : 0 < w.length) {t : ℕ}
    (g : ResidueGroup t → ℝ) {y : ResidueGroup (t + w.length)} (hy : ¬ IsResidueUnit y) :
    transfer w g y = 0 := by
  rw [transfer_apply, sum_eq_zero, mul_zero]
  intro z hz
  rw [mem_filter] at hz
  exact absurd (hz.2 ▸ isResidueUnit_residueMap hw t z) hy

end CollatzPosDens
