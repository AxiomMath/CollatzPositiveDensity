/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.SeedShift
public import Mathlib.Tactic.NormNum

/-!
# Seed exponents and seed candidates

For a target `t`, the seed exponent `e_0(t)` is `σ_sd + 2` if `t ≡ 1 (mod 3)` and `σ_sd + 3`
otherwise, where `σ_sd` is the seed shift `seedShift` (`σ_sd = 66176`, so
`e_0(t) ∈ {66178, 66179}`). Since `σ_sd` is even, `2^{σ_sd + 2} ≡ 1 (mod 3)`, and the exponent is
chosen so that `2^{e_0(t)} t ≡ 1 (mod 3)` whenever `3 ∤ t`. The seed candidates are
$$\mathsf c_t(v) = \bigl\lfloor (2^{e_0(t) + 2v} t - 1)/3 \bigr\rfloor \in \mathbb{N}
\qquad (t \ge 1,\ v \ge 0).$$

## Main definitions

* `CollatzPosDens.seedExponent t`: the seed exponent `e_0(t)`.
* `CollatzPosDens.seedCandidate t v`: the seed candidate `𝖼_t(v)`.

## Main results

* `CollatzPosDens.seedExponent_of_mod_eq_one`, `CollatzPosDens.seedExponent_of_mod_ne_one`:
  the two cases of `e_0(t)`.
* `CollatzPosDens.seedExponent_bounds`: `σ_sd + 2 ≤ e_0(t) ≤ σ_sd + 3`.
* `CollatzPosDens.two_pow_seedExponent_mul_mod_three`: `2^{e_0(t)} t ≡ 1 (mod 3)` if `3 ∤ t`.

## Implementation notes

The quotient is natural-number division and the subtraction is truncated subtraction of `ℕ`,
which is the floor of the rational quotient for `t ≥ 1`. The seed exponent is defined on
natural numbers: it is only ever evaluated at targets `t ≥ 1`, where it agrees with the
residue-class definition on the integers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The seed exponent `e_0(t)`: `σ_sd + 2` if `t ≡ 1 (mod 3)`, and `σ_sd + 3` otherwise. -/
@[collatz_pos_dens "def_seed_exponent"]
def seedExponent (t : ℕ) : ℕ :=
  if t % 3 = 1 then seedShift + 2 else seedShift + 3

/-- The seed candidate `𝖼_t(v) = ⌊(2^{e_0(t) + 2v} t - 1)/3⌋`. -/
@[collatz_pos_dens "def_seed_candidate"]
def seedCandidate (t v : ℕ) : ℕ :=
  (2 ^ (seedExponent t + 2 * v) * t - 1) / 3

/-- `e_0(t) = σ_sd + 2` if `t ≡ 1 (mod 3)`. -/
theorem seedExponent_of_mod_eq_one {t : ℕ} (ht : t % 3 = 1) :
    seedExponent t = seedShift + 2 := ite_eq_left_iff.mpr fun h => absurd ht h

/-- `e_0(t) = σ_sd + 3` if `t ≢ 1 (mod 3)`. -/
theorem seedExponent_of_mod_ne_one {t : ℕ} (ht : t % 3 ≠ 1) :
    seedExponent t = seedShift + 3 := ite_eq_right_iff.mpr fun h => absurd h ht

/-- `σ_sd + 2 ≤ e_0(t) ≤ σ_sd + 3`. -/
theorem seedExponent_bounds (t : ℕ) :
    seedShift + 2 ≤ seedExponent t ∧ seedExponent t ≤ seedShift + 3 := by
  unfold seedExponent
  split_ifs <;> omega

/-- `2^{σ_sd + 2} ≡ 1 (mod 3)`, as `σ_sd + 2` is even. -/
theorem two_pow_seedShift_add_two_mod_three : 2 ^ (seedShift + 2) % 3 = 1 := by
  rw [seedShift_eq, show 66176 + 2 = 2 * 33089 from rfl, pow_mul, Nat.pow_mod]
  norm_num

/-- If `3 ∤ t`, then `2^{e_0(t)} t ≡ 1 (mod 3)`. -/
theorem two_pow_seedExponent_mul_mod_three {t : ℕ} (ht : ¬ 3 ∣ t) :
    2 ^ seedExponent t * t % 3 = 1 := by
  have h := two_pow_seedShift_add_two_mod_three
  by_cases h1 : t % 3 = 1
  · rw [seedExponent_of_mod_eq_one h1, Nat.mul_mod, h, h1]
  · have h2 : t % 3 = 2 := by omega
    rw [seedExponent_of_mod_ne_one h1, show seedShift + 3 = (seedShift + 2) + 1 by omega,
      pow_succ, Nat.mul_mod, Nat.mul_mod (2 ^ (seedShift + 2)), h, h2]

end CollatzPosDens
