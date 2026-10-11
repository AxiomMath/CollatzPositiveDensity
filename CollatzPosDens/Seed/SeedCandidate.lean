/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Tactic.NormNum

/-!
# Seed exponents and seed candidates

For an endpoint `s`, the seed exponent `e_0(s)` is `38` if `s ≡ 1 (mod 3)` and `39` otherwise,
chosen so that `2^{e_0(s)} s ≡ 1 (mod 3)` whenever `3 ∤ s`. The seed candidates are
$$\mathsf M_s(v) = \bigl\lfloor (2^{e_0(s) + 2v} s - 1)/3 \bigr\rfloor \in \mathbb{N}
\qquad (v \ge 0).$$

## Main definitions

* `CollatzPosDens.seedExponent s`: the seed exponent `e_0(s)`.
* `CollatzPosDens.seedCandidate s v`: the seed candidate `𝖬_s(v)`.

## Implementation notes

The quotient is natural-number division and the subtraction is truncated subtraction of `ℕ`,
which is the floor of the corresponding rational quotient for `s ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The seed exponent `e_0(s)`: `38` if `s ≡ 1 (mod 3)`, and `39` otherwise. -/
@[collatz_pos_dens "def_seed_exponent"]
def seedExponent (s : ℕ) : ℕ :=
  if s % 3 = 1 then 38 else 39

/-- The seed candidate `𝖬_s(v) = ⌊(2^{e_0(s) + 2v} s - 1)/3⌋`. -/
@[collatz_pos_dens "def_seed_candidate"]
def seedCandidate (s v : ℕ) : ℕ :=
  (2 ^ (seedExponent s + 2 * v) * s - 1) / 3

end CollatzPosDens
