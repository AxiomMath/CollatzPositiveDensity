/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Cost

/-!
# The height-seventeen crossing cost

For integers `c`, `o` and a real `x`, the crossing cost is
`xc_{c,o}(x) = Φ^cap_c(x / 2^o)` if `c ∈ {4, 5}`, and
`xc_{c,o}(x) = Φ^cap_c(x / 2^o) · cf_o(9x)` if `c ∉ {4, 5}`,
where `Φ^cap_c` is the capped packet factor `CollatzPosDens.trCapFactor` and `cf_o` the
height-seventeen future cost `CollatzPosDens.c3H17Cost`.

## Main definitions

* `CollatzPosDens.c3H17FirstCost`: the crossing cost `xc_{c,o}(x)`.

## Main results

* `CollatzPosDens.c3H17FirstCost_of_mem`: the value `Φ^cap_c(x / 2^o)` for `c ∈ {4, 5}`.
* `CollatzPosDens.c3H17FirstCost_of_not_mem`: the value `Φ^cap_c(x / 2^o) · cf_o(9x)` for
  `c ∉ {4, 5}`.
* `CollatzPosDens.c3H17FirstCost_of_le`: the value `Φ^cap_c(x / 2^o)` for `o ≥ 15`.

## Implementation notes

The crossing cost is defined for every integer `o`, not only for `o ≥ 1`, with `2^o` an
integer power of `2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The height-seventeen crossing cost: `xc_{c,o}(x) = Φ^cap_c(x / 2^o)` if `c ∈ {4, 5}`, and
`xc_{c,o}(x) = Φ^cap_c(x / 2^o) · cf_o(9x)` otherwise. -/
@[collatz_pos_dens "def_c3_h17_first_cost"]
noncomputable def c3H17FirstCost (c o : ℤ) (x : ℝ) : ℝ :=
  if c ∈ ({4, 5} : Finset ℤ) then trCapFactor c (x / (2 : ℝ) ^ o)
  else trCapFactor c (x / (2 : ℝ) ^ o) * c3H17Cost o (9 * x)

/-- The crossing cost for `c ∈ {4, 5}`. -/
theorem c3H17FirstCost_of_mem {c : ℤ} (hc : c ∈ ({4, 5} : Finset ℤ)) (o : ℤ) (x : ℝ) :
    c3H17FirstCost c o x = trCapFactor c (x / (2 : ℝ) ^ o) :=
  ite_eq_left_of_eq_true _ _ (eq_true hc)

/-- The crossing cost for `c ∉ {4, 5}`. -/
theorem c3H17FirstCost_of_not_mem {c : ℤ} (hc : c ∉ ({4, 5} : Finset ℤ)) (o : ℤ) (x : ℝ) :
    c3H17FirstCost c o x = trCapFactor c (x / (2 : ℝ) ^ o) * c3H17Cost o (9 * x) :=
  ite_eq_right_of_eq_false _ _ (eq_false hc)

/-- The crossing cost from height `15` on is the capped packet factor alone. -/
theorem c3H17FirstCost_of_le (c : ℤ) {o : ℤ} (ho : 15 ≤ o) (x : ℝ) :
    c3H17FirstCost c o x = trCapFactor c (x / (2 : ℝ) ^ o) := by
  unfold c3H17FirstCost
  split_ifs <;> simp [c3H17Cost_of_le ho]

end CollatzPosDens
