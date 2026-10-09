/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Bht
public import CollatzPosDens.Recipe.CalM

/-!
# The cutoff `X_0`

This file defines the natural number
$$X_0 = 32\,(2^{B_{\mathrm{ht}}}\mathcal{M} + 1) \in \mathbb{N},$$
where `B_ht` is the height exponent `heightExponent` and `𝓜` is the seed bound `seedBound`.

## Main definitions

* `CollatzPosDens.cutoffOf`: the expression `32 * (2 ^ B * M + 1)` in parameters `B`, `M`.
* `CollatzPosDens.cutoff`: the cutoff `X_0`, its value at `B = B_ht`, `M = 𝓜`.

## Main results

* `CollatzPosDens.cutoff_def`: the defining formula `X_0 = 32 (2 ^ B_ht 𝓜 + 1)`.
* `CollatzPosDens.cutoff_pos`: `0 < X_0`.
* `CollatzPosDens.seedBound_lt_cutoff`: `𝓜 < X_0`.

## Implementation notes

The cutoff is far too large to be evaluated, so `cutoff` is irreducible and is meant to be
used through `cutoff_def`. It is the value of the parametric expression `cutoffOf`, whose
elementary facts are proved with the parameters left symbolic.

## References

* [Mazur, *Collatz positive density*], §16.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `32 * (2 ^ B * M + 1)` with parameters `B` and `M`. -/
def cutoffOf (B M : ℕ) : ℕ := 32 * (2 ^ B * M + 1)

/-- The defining formula of `cutoffOf`. -/
theorem cutoffOf_def (B M : ℕ) : cutoffOf B M = 32 * (2 ^ B * M + 1) := rfl

/-- `cutoffOf B M` is positive. -/
theorem cutoffOf_pos (B M : ℕ) : 0 < cutoffOf B M := by
  rw [cutoffOf_def]
  omega

/-- `M < cutoffOf B M`. -/
theorem lt_cutoffOf (B M : ℕ) : M < cutoffOf B M := by
  rw [cutoffOf_def]
  have : M ≤ 2 ^ B * M := Nat.le_mul_of_pos_left M (Nat.two_pow_pos B)
  omega

/-- `cutoffOf` is monotone in both parameters. -/
theorem cutoffOf_mono {B B' M M' : ℕ} (hB : B ≤ B') (hM : M ≤ M') :
    cutoffOf B M ≤ cutoffOf B' M' := by
  rw [cutoffOf_def, cutoffOf_def]
  have := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num : 0 < 2) hB) hM
  omega

/-- The cutoff `X_0 = 32 (2 ^ B_ht 𝓜 + 1) ∈ ℕ`, where `B_ht` is the height exponent
`heightExponent` and `𝓜` the seed bound `seedBound`. -/
@[collatz_pos_dens "def_X0", irreducible]
noncomputable def cutoff : ℕ := cutoffOf heightExponent seedBound

/-- `X_0` is `cutoffOf` at `B = B_ht` and `M = 𝓜`. -/
theorem cutoff_eq_cutoffOf : cutoff = cutoffOf heightExponent seedBound := by
  unfold cutoff
  rfl

/-- The defining formula `X_0 = 32 (2 ^ B_ht 𝓜 + 1)`. -/
theorem cutoff_def : cutoff = 32 * (2 ^ heightExponent * seedBound + 1) :=
  cutoff_eq_cutoffOf.trans (cutoffOf_def _ _)

/-- The cutoff is positive. -/
theorem cutoff_pos : 0 < cutoff :=
  cutoff_eq_cutoffOf ▸ cutoffOf_pos _ _

/-- The seed bound lies below the cutoff. -/
theorem seedBound_lt_cutoff : seedBound < cutoff :=
  cutoff_eq_cutoffOf ▸ lt_cutoffOf _ _

end CollatzPosDens
