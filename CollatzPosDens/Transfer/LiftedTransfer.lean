/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Reduction
public import CollatzPosDens.Transfer.Transfer

/-!
# The lifted transfer operator

For a word `w` of length `d`, integers `k ≥ 0` and `Q ≥ d + k`, and `g : G_k → ℝ`, the lifted
transfer is `𝒯_{w,Q} g := 𝒯_w (g ∘ π_{Q-d,k}) : G_Q → ℝ`: first pull `g` back to `G_{Q-d}`
along the reduction `π_{Q-d,k}`, then apply the transfer operator `𝒯_w`, which lands in
`G_{(Q-d)+d} = G_Q`.

## Main definitions

* `CollatzPosDens.liftedTransfer w h g`: for `h : |w| + k ≤ Q`, the function
  `𝒯_{w,Q} g : G_Q → ℝ`.

## Main results

* `CollatzPosDens.liftedTransfer_add`, `CollatzPosDens.liftedTransfer_smul`: `𝒯_{w,Q}` is
  linear in `g`.
* `CollatzPosDens.sum_liftedTransfer`:
  `∑_y (𝒯_{w,Q} g)(y) = ω(w) ∑_{z ∈ G_{Q-d}} g(π_{Q-d,k} z)`.
* `CollatzPosDens.liftedTransfer_nonneg`: `𝒯_{w,Q}` preserves nonnegativity.

## Implementation notes

The transfer `𝒯_w` of a function on `G_{Q-d}` is a function on `G_{(Q-d)+d}`, a type that is
only propositionally equal to `G_Q`. We identify the two through the reduction
`π_{Q,(Q-d)+d}`, which is a ring isomorphism since the two moduli coincide.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The lifted transfer `𝒯_{w,Q} g := 𝒯_w (g ∘ π_{Q-d,k}) : G_Q → ℝ` of `g : G_k → ℝ`, for a
word `w` of length `d` and `d + k ≤ Q`. The target `G_{(Q-d)+d}` of `𝒯_w` is identified with
`G_Q` through the reduction map between these equal moduli. -/
@[collatz_pos_dens "def_s02_lifted_transfer"]
noncomputable def liftedTransfer (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q)
    (g : ResidueGroup k → ℝ) (y : ResidueGroup Q) : ℝ :=
  transfer w (g ∘ residueReduction (Nat.le_sub_of_add_le' h))
    (residueReduction (Nat.sub_add_cancel (le_of_add_le_left h)).le y)

/-- Unfolding lemma for `liftedTransfer`. -/
theorem liftedTransfer_apply (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q)
    (g : ResidueGroup k → ℝ) (y : ResidueGroup Q) :
    liftedTransfer w h g y = transfer w (g ∘ residueReduction (Nat.le_sub_of_add_le' h))
      (residueReduction (Nat.sub_add_cancel (le_of_add_le_left h)).le y) :=
  rfl

/-- The lifted transfer operator is additive. -/
theorem liftedTransfer_add (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q)
    (f g : ResidueGroup k → ℝ) :
    liftedTransfer w h (f + g) = liftedTransfer w h f + liftedTransfer w h g := by
  ext y
  simp only [liftedTransfer_apply, Pi.add_apply]
  rw [show (f + g) ∘ residueReduction (Nat.le_sub_of_add_le' h) =
      f ∘ residueReduction (Nat.le_sub_of_add_le' h) +
        g ∘ residueReduction (Nat.le_sub_of_add_le' h) from rfl, transfer_add]
  rfl

/-- The lifted transfer operator commutes with scalar multiplication. -/
theorem liftedTransfer_smul (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q) (c : ℝ)
    (g : ResidueGroup k → ℝ) :
    liftedTransfer w h (c • g) = c • liftedTransfer w h g := by
  ext y
  simp only [liftedTransfer_apply, Pi.smul_apply]
  rw [show (c • g) ∘ residueReduction (Nat.le_sub_of_add_le' h) =
      c • (g ∘ residueReduction (Nat.le_sub_of_add_le' h)) from rfl, transfer_smul]
  rfl

/-- The lifted transfer of the zero function is zero. -/
@[simp]
theorem liftedTransfer_zero (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q) :
    liftedTransfer w h (0 : ResidueGroup k → ℝ) = 0 := by
  ext y
  simp only [liftedTransfer_apply, Pi.zero_apply]
  rw [show (0 : ResidueGroup k → ℝ) ∘ residueReduction (Nat.le_sub_of_add_le' h) = 0 from rfl,
    transfer_zero]
  rfl

/-- The total mass of `𝒯_{w,Q} g` is `ω(w)` times the mass of the pullback of `g` to
`G_{Q-d}`: `∑_y (𝒯_{w,Q} g)(y) = ω(w) ∑_{z ∈ G_{Q-d}} g(π_{Q-d,k} z)`. -/
theorem sum_liftedTransfer (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q)
    (g : ResidueGroup k → ℝ) :
    ∑ y, liftedTransfer w h g y =
      (w.weight : ℝ) * ∑ z, g (residueReduction (Nat.le_sub_of_add_le' h) z) := by
  have hQ := Nat.sub_add_cancel (le_of_add_le_left h)
  have hbij : Function.Bijective (residueReduction hQ.le) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨residueReduction hQ.ge, fun y => ?_, fun y => ?_⟩ <;>
      simp
  simp only [liftedTransfer_apply]
  rw [Function.Bijective.sum_comp hbij (transfer w _), sum_transfer]
  rfl

/-- The lifted transfer of a nonnegative function is nonnegative. -/
theorem liftedTransfer_nonneg (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q)
    {g : ResidueGroup k → ℝ} (hg : 0 ≤ g) (y : ResidueGroup Q) :
    0 ≤ liftedTransfer w h g y :=
  transfer_nonneg w (g := g ∘ residueReduction (Nat.le_sub_of_add_le' h)) (fun _ => hg _) _

end CollatzPosDens
