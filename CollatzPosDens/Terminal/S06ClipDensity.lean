/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Terminal.S06ClipWords

/-!
# The clipped subdensity

For integers `m ≥ 1`, `n ≥ 2` and a real `B > 0`, the *clipped subdensity*
`g^clp_{m,n,B} : G_m → ℝ` is the rescaled submass of the clipped words,
$$g^{\mathrm{clp}}_{m,n,B}(y) = 3^m \, \mathrm{Sub}^m_{\mathcal V^{\mathrm{clp}}_{m,n,B}}(y)^{ℝ},$$
where `x^ℝ` is `x` for `x < ∞` and `0` for `x = ∞`, as in `CollatzPosDens.refDensity`.

## Main definitions

* `CollatzPosDens.clipDensity m n B`: the clipped subdensity `g^clp_{m,n,B}`.

## Main results

* `CollatzPosDens.clipDensity_nonneg`: `0 ≤ g^clp_{m,n,B}(y)`.

## Implementation notes

The coercion `x ↦ x^ℝ` is `ENNReal.toReal`, as in `CollatzPosDens.refDensity`.

## References

* [Mazur, *Collatz positive density*], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipped subdensity `g^clp_{m,n,B}(y) = 3^m Sub^m_{𝒱^clp_{m,n,B}}(y)^ℝ` on `G_m`,
where `x^ℝ` is `ENNReal.toReal x`. -/
@[collatz_pos_dens "def_s06_clip_density"]
noncomputable def clipDensity (m n : ℕ) (B : ℝ) (y : ResidueGroup m) : ℝ :=
  3 ^ m * (subMass m (clipWords m n B) y).toReal

/-- `clipDensity m n B y` is `3 ^ m` times the real value of the submass of
`clipWords m n B` at `y`. -/
theorem clipDensity_def (m n : ℕ) (B : ℝ) (y : ResidueGroup m) :
    clipDensity m n B y = 3 ^ m * (subMass m (clipWords m n B) y).toReal :=
  rfl

/-- The clipped subdensity is nonnegative. -/
theorem clipDensity_nonneg (m n : ℕ) (B : ℝ) (y : ResidueGroup m) :
    0 ≤ clipDensity m n B y := by
  unfold clipDensity
  positivity

end CollatzPosDens
