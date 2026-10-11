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
# The construction's cutoff `X_0(s)`

For an endpoint parameter `s ≥ 1`, this file defines the cutoff of the construction,
$$X_0(s) = 32\,(2^{B_{\mathrm{ht}}(s)}\mathcal{M}(s) + 1) \in \mathbb{N},$$
where `B_ht(s)` is the height exponent and `𝓜(s)` is the seed allowance. Beyond `X_0(s)` the
main proposition gives a positive proportion of odd starting values reaching `s`.

## Main definitions

* `CollatzPosDens.cutoffOf`: the expression `32 * (2 ^ B * M + 1)` in parameters `B`, `M`.
* `CollatzPosDens.cutoff`: the cutoff `X_0(s)`, its value at `B = B_ht(s)`, `M = 𝓜(s)`.

## Main results

* `CollatzPosDens.cutoff_def`: the defining formula `X_0(s) = 32 (2 ^ B_ht(s) 𝓜(s) + 1)`.
* `CollatzPosDens.cutoff_pos`: `0 < X_0(s)`.
* `CollatzPosDens.seedBound_lt_cutoff`: `𝓜(s) < X_0(s)`.

## Implementation notes

The cutoff is far too large to be evaluated, so `cutoff` is irreducible and is meant to be
used through `cutoff_def`. It is the value of the parametric expression `cutoffOf`, whose
elementary facts are proved with the parameters left symbolic.

## References

* [Mazur, *Collatz positive density*], §16.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The expression `32 * (2 ^ B * M + 1)` with parameters `B` and `M`.
The cutoff `X_0(s)` is `cutoffOf B_ht(s) 𝓜(s)`. -/
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

/-- **The construction's cutoff** `X_0(s) = 32 (2 ^ B_ht(s) 𝓜(s) + 1) ∈ ℕ`, where `B_ht(s)` is the
height exponent and `𝓜(s)` the seed allowance. It is irreducible so that tactics never try to
evaluate it; use `cutoff_def`. -/
@[collatz_pos_dens "def_X0", irreducible]
noncomputable def cutoff (s : ℕ) : ℕ := cutoffOf (heightExponent s) (seedBound s)

/-- `X_0(s)` is `cutoffOf` at `B = B_ht(s)` and `M = 𝓜(s)`. -/
theorem cutoff_eq_cutoffOf (s : ℕ) : cutoff s = cutoffOf (heightExponent s) (seedBound s) := by
  unfold cutoff
  rfl

/-- The defining formula `X_0(s) = 32 (2 ^ B_ht(s) 𝓜(s) + 1)`. -/
theorem cutoff_def (s : ℕ) : cutoff s = 32 * (2 ^ heightExponent s * seedBound s + 1) :=
  (cutoff_eq_cutoffOf s).trans (cutoffOf_def _ _)

/-- The cutoff is positive. -/
theorem cutoff_pos (s : ℕ) : 0 < cutoff s :=
  (cutoff_eq_cutoffOf s) ▸ cutoffOf_pos _ _

/-- The seed allowance lies below the cutoff. -/
theorem seedBound_lt_cutoff (s : ℕ) : seedBound s < cutoff s :=
  (cutoff_eq_cutoffOf s) ▸ lt_cutoffOf _ _

end CollatzPosDens
