/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueMap

/-!
# The transfer operator of a word

For a word `w` of length `d`, `t ∈ ℕ` and a real function `g : G_t → ℝ`, the transfer
`𝒯_w g : G_{t+d} → ℝ` is the weighted pushforward of `g` along the residue map
`φ_w : G_t → G_{t+d}`:
`(𝒯_w g)(y) = ω(w) · ∑_{z ∈ G_t, φ_w(z) = y} g(z)`, a finite sum since `G_t` is finite.

## Main definitions

* `CollatzPosDens.transfer w g`: the function `𝒯_w g : G_{t+|w|} → ℝ`.

## Main results

* `CollatzPosDens.transfer_add`, `CollatzPosDens.transfer_smul`: `𝒯_w` is linear in `g`.
* `CollatzPosDens.sum_transfer`: `∑_y (𝒯_w g)(y) = ω(w) ∑_z g(z)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The transfer operator `(𝒯_w g)(y) = ω(w) · ∑_{z ∈ G_t, φ_w(z) = y} g(z)` of a word `w`,
sending `g : G_t → ℝ` to a function on `G_{t+|w|}`. -/
@[collatz_pos_dens "def_transfer"]
noncomputable def transfer (w : Word) {t : ℕ} (g : ResidueGroup t → ℝ)
    (y : ResidueGroup (t + w.length)) : ℝ :=
  (w.weight : ℝ) * ∑ z with residueMap w t z = y, g z

/-- Unfolding lemma for `transfer`. -/
theorem transfer_apply (w : Word) {t : ℕ} (g : ResidueGroup t → ℝ)
    (y : ResidueGroup (t + w.length)) :
    transfer w g y = (w.weight : ℝ) * ∑ z with residueMap w t z = y, g z :=
  rfl

/-- The transfer operator is additive. -/
theorem transfer_add (w : Word) {t : ℕ} (f g : ResidueGroup t → ℝ) :
    transfer w (f + g) = transfer w f + transfer w g := by
  ext y
  simp [transfer_apply, sum_add_distrib, mul_add]

/-- The transfer operator commutes with scalar multiplication. -/
theorem transfer_smul (w : Word) {t : ℕ} (c : ℝ) (g : ResidueGroup t → ℝ) :
    transfer w (c • g) = c • transfer w g := by
  ext y
  simp only [transfer_apply, Pi.smul_apply, smul_eq_mul, ← mul_sum]
  ring

/-- The transfer of the zero function is zero. -/
@[simp]
theorem transfer_zero (w : Word) {t : ℕ} :
    transfer w (0 : ResidueGroup t → ℝ) = 0 := by
  ext y
  simp [transfer_apply]

/-- The total mass of `𝒯_w g` is `ω(w)` times that of `g`:
`∑_y (𝒯_w g)(y) = ω(w) ∑_z g(z)`. -/
theorem sum_transfer (w : Word) {t : ℕ} (g : ResidueGroup t → ℝ) :
    ∑ y, transfer w g y = (w.weight : ℝ) * ∑ z, g z := by
  simp only [transfer_apply, ← mul_sum]
  rw [sum_fiberwise]

/-- The transfer of a nonnegative function is nonnegative. -/
theorem transfer_nonneg (w : Word) {t : ℕ} {g : ResidueGroup t → ℝ} (hg : 0 ≤ g)
    (y : ResidueGroup (t + w.length)) : 0 ≤ transfer w g y :=
  mul_nonneg (by exact_mod_cast w.weight_pos.le) (sum_nonneg fun z _ => hg z)

end CollatzPosDens
