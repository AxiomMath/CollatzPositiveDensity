/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.S02Reduction
public import CollatzPosDens.Terminal.S06ClipDensity

/-!
# The clipping remainder

For integers `q ≥ 1`, `n ≥ 2` and a real `B > 0`, the *clipping remainder*
`Φ^clp_{q,n,B} : G_q → ℝ` is what remains of the reference density `ρ_q` after the clipped
subdensity at the level `min(q, n)` is removed:
$$\Phi^{\mathrm{clp}}_{q,n,B}(y) = \rho_q(y) - g^{\mathrm{clp}}_{q,n,B}(y) \quad (q ≤ n),$$
$$\Phi^{\mathrm{clp}}_{q,n,B}(y) = \rho_n(\pi_{q,n} y) - g^{\mathrm{clp}}_{n,n,B}(\pi_{q,n} y)
  + |\rho_q(y) - \rho_n(\pi_{q,n} y)| \quad (q > n).$$
When `q > n` the last term is the mixing defect between the levels `q` and `n`.

## Main definitions

* `CollatzPosDens.clipRemainder q n B`: the clipping remainder `Φ^clp_{q,n,B}`.

## Main results

* `CollatzPosDens.clipRemainder_of_le`: the formula for `q ≤ n`.
* `CollatzPosDens.clipRemainder_of_lt`: the formula for `q > n`.
* `CollatzPosDens.clipRemainder_of_ge`: the second formula also holds for `q = n`, hence for
  every `q ≥ n`.

## Implementation notes

The two cases are a dependent `if` on `q ≤ n`, so that the reduction `π_{q,n}` receives the
proof of `n ≤ q` obtained from the negated condition.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping remainder `Φ^clp_{q,n,B} : G_q → ℝ`: `ρ_q(y) - g^clp_{q,n,B}(y)` if `q ≤ n`,
and `ρ_n(π_{q,n} y) - g^clp_{n,n,B}(π_{q,n} y) + |ρ_q(y) - ρ_n(π_{q,n} y)|` if `q > n`. -/
@[collatz_pos_dens "def_s06_clip_remainder"]
noncomputable def clipRemainder (q n : ℕ) (B : ℝ) (y : ResidueGroup q) : ℝ :=
  if h : q ≤ n then refDensity q y - clipDensity q n B y
  else
    refDensity n (residueReduction (le_of_not_ge h) y) -
        clipDensity n n B (residueReduction (le_of_not_ge h) y) +
      |refDensity q y - refDensity n (residueReduction (le_of_not_ge h) y)|

/-- The clipping remainder for `q ≤ n`: `Φ^clp_{q,n,B}(y) = ρ_q(y) - g^clp_{q,n,B}(y)`. -/
theorem clipRemainder_of_le {q n : ℕ} (h : q ≤ n) (B : ℝ) (y : ResidueGroup q) :
    clipRemainder q n B y = refDensity q y - clipDensity q n B y := by
  simp [clipRemainder, h]

/-- The clipping remainder for `q > n`: `Φ^clp_{q,n,B}(y) = ρ_n(π_{q,n} y) -
g^clp_{n,n,B}(π_{q,n} y) + |ρ_q(y) - ρ_n(π_{q,n} y)|`. -/
theorem clipRemainder_of_lt {q n : ℕ} (h : n < q) (B : ℝ) (y : ResidueGroup q) :
    clipRemainder q n B y =
      refDensity n (residueReduction h.le y) - clipDensity n n B (residueReduction h.le y) +
        |refDensity q y - refDensity n (residueReduction h.le y)| := by
  simp [clipRemainder, not_le.2 h]

/-- The formula of the case `q > n` holds for every `q ≥ n`: at `q = n` the reduction is the
identity and the defect term vanishes. -/
theorem clipRemainder_of_ge {q n : ℕ} (h : n ≤ q) (B : ℝ) (y : ResidueGroup q) :
    clipRemainder q n B y =
      refDensity n (residueReduction h y) - clipDensity n n B (residueReduction h y) +
        |refDensity q y - refDensity n (residueReduction h y)| := by
  rcases h.lt_or_eq with h' | rfl
  · exact clipRemainder_of_lt h' B y
  · simp [clipRemainder_of_le le_rfl, residueReduction_self]

end CollatzPosDens
