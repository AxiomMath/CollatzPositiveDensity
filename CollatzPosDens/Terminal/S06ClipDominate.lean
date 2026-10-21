/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06ClipRemainder

/-!
# Finite clipping

For every `y ∈ G_q`, the reference density is dominated by the clipped subdensity at the level
`min(q, n)` plus the clipping remainder:
$$\rho_q(y) \le g^{\mathrm{clp}}_{\min(q,n),n,B}\bigl(\pi_{q,\min(q,n)}(y)\bigr)
  + \Phi^{\mathrm{clp}}_{q,n,B}(y).$$
If `q ≤ n` this is an equality, as `π_{q,q}` is the identity; if `q > n` it is
`ρ_q(y) ≤ ρ_n(x) + |ρ_q(y) - ρ_n(x)|` with `x = π_{q,n} y`.

## Main results

* `CollatzPosDens.refDensity_le_clipDensity_add_clipRemainder`: the reference density `ρ_q(y)`
  is at most the clipped subdensity at level `min(q, n)` plus the clipping remainder.

## Implementation notes

The bound is usually stated for `q ≥ 1`, `n ≥ 2` and `B > 0`; it holds for all `q, n ∈ ℕ` and
real `B`, and is stated so.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Finite clipping.** For every `y ∈ G_q`,
`ρ_q(y) ≤ g^clp_{min(q,n),n,B}(π_{q,min(q,n)} y) + Φ^clp_{q,n,B}(y)`. -/
@[collatz_pos_dens "lem_s06_clip_dominate"]
theorem refDensity_le_clipDensity_add_clipRemainder (q n : ℕ) (B : ℝ) (y : ResidueGroup q) :
    refDensity q y ≤
      clipDensity (min q n) n B (residueReduction (min_le_left q n) y) +
        clipRemainder q n B y := by
  rcases le_or_gt q n with h | h
  · have hm : min q n = q := min_eq_left h
    rw [clipRemainder_of_le h]
    have key : ∀ (k : ℕ) (hk : k = q),
        clipDensity k n B (residueReduction (hk ▸ le_refl q) y) =
          clipDensity q n B y := by
      rintro k rfl
      rw [residueReduction_self]
    rw [key (min q n) hm]
    linarith
  · have hm : min q n = n := min_eq_right h.le
    rw [clipRemainder_of_lt h]
    have key : ∀ (k : ℕ) (hk : k = n),
        clipDensity k n B (residueReduction (hk ▸ h.le) y) =
          clipDensity n n B (residueReduction h.le y) := by
      rintro k rfl
      rfl
    rw [key (min q n) hm]
    linarith [le_abs_self (refDensity q y - refDensity n (residueReduction h.le y))]

end CollatzPosDens
