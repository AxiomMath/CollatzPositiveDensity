/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3NarrowDeficit
public import CollatzPosDens.Case3.C3H17CapUp
public import CollatzPosDens.Case3.C3H17Lip
public import CollatzPosDens.Case3.C3H17Node
public import CollatzPosDens.StoppingTrace.TrLipConst

/-!
# The height-seventeen cost table

For integers `c, o` with `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and an odd integer `m`, the cost table
`ct_{c,o}(m)` is the least of the following rationals:

* `1`;
* if `c ≥ 3`, the *packet value* `1 - δ'_{c,o}`, where `δ'_{c,o}` is the narrow deficit;
* if `c ≥ 3`, the *direct value* `Ū_c(m / 2^o) + 10^{-8} ⌈10^8 · 10^{-6} ℓ_c 2^{-o}⌉`,
  where `Ū_c` is the grid majorant of the capped packet factor and `ℓ_c` its Lipschitz constant;
* if `c ∉ {4, 5}`, the *joint value*
  `10^{-8} ⌈10^8 Ū_c(m / 2^o) G⁺⌉ + 10^{-8} ⌈10^8 · 10^{-6} (ℓ_c 2^{-o} + 9 𝖫_o)⌉`,
  where `G⁺ = cf⁺_o(9m)` is the rounded future cost (equal to `1` for `o ≥ 15`) and `𝖫_o` the
  Lipschitz constant of the future cost.

Each listed number bounds the crossing cost `xc_{c,o}` on the whole cell `|x - m| ≤ 10^{-6}`, so
`ct_{c,o}(m)` is a rational majorant of it.

## Main definitions

* `CollatzPosDens.c3H17Table`: the cost table `ct_{c,o}(m)`.

## Main results

* `CollatzPosDens.c3H17Table_le_one`, `CollatzPosDens.c3H17Table_le_packet`,
  `CollatzPosDens.c3H17Table_le_direct`, `CollatzPosDens.c3H17Table_le_joint`: the table is at most
  each listed number.
* `CollatzPosDens.le_c3H17Table`: a rational at most every listed number is at most the table, so
  the table is the least of them.

## Implementation notes

The table is computable and rational-valued. A number that is not listed (the packet and direct
values for `c ≤ 2`, the joint value for `c ∈ {4, 5}`) is replaced by `1`, which is listed and so
does not change the minimum. The rounding `10^{-8} ⌈10^8 x⌉` is written `⌈10^8 x⌉ / 10^8`. The
indices `c, o, m` range over all of `ℤ`, and the same formula is used outside the range
`2 ≤ c ≤ 16`, `1 ≤ o ≤ c`, `m` odd, where the table is otherwise undefined.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The height-seventeen cost table `ct_{c,o}(m)`: the least of `1`; if `c ≥ 3`, the packet value
`1 - δ'_{c,o}` and the direct value `Ū_c(m / 2^o) + 10^{-8} ⌈10^8 · 10^{-6} ℓ_c 2^{-o}⌉`; and, if
`c ∉ {4, 5}`, the joint value
`10^{-8} ⌈10^8 Ū_c(m / 2^o) cf⁺_o(9m)⌉ + 10^{-8} ⌈10^8 · 10^{-6} (ℓ_c 2^{-o} + 9 𝖫_o)⌉`. -/
@[collatz_pos_dens "def_c3_h17_table"]
def c3H17Table (c o m : ℤ) : ℚ :=
  min (min 1
      (if 3 ≤ c then
        min (1 - c3NarrowDeficit c o)
          (c3H17CapUp c ((m : ℚ) / 2 ^ o) +
            (⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o)))⌉ : ℚ) / 10 ^ 8)
      else 1))
    (if c ∉ ({4, 5} : Finset ℤ) then
      (⌈(10 ^ 8 : ℚ) * (c3H17CapUp c ((m : ℚ) / 2 ^ o) * c3H17Node o (9 * m))⌉ : ℚ) / 10 ^ 8 +
        (⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o) + 9 * c3H17Lip o))⌉ : ℚ) /
          10 ^ 8
    else 1)

/-- The table is at most `1`. -/
theorem c3H17Table_le_one (c o m : ℤ) : c3H17Table c o m ≤ 1 :=
  (min_le_left _ _).trans (min_le_left _ _)

/-- The table is at most the packet value `1 - δ'_{c,o}` for `c ≥ 3`. -/
theorem c3H17Table_le_packet {c : ℤ} (hc : 3 ≤ c) (o m : ℤ) :
    c3H17Table c o m ≤ 1 - c3NarrowDeficit c o := by
  unfold c3H17Table
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
  exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

/-- The table is at most the direct value for `c ≥ 3`. -/
theorem c3H17Table_le_direct {c : ℤ} (hc : 3 ≤ c) (o m : ℤ) :
    c3H17Table c o m ≤ c3H17CapUp c ((m : ℚ) / 2 ^ o) +
      (⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o)))⌉ : ℚ) / 10 ^ 8 := by
  unfold c3H17Table
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
  exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- The table is at most the joint value for `c ∉ {4, 5}`. -/
theorem c3H17Table_le_joint {c : ℤ} (hc : c ∉ ({4, 5} : Finset ℤ)) (o m : ℤ) :
    c3H17Table c o m ≤
      (⌈(10 ^ 8 : ℚ) * (c3H17CapUp c ((m : ℚ) / 2 ^ o) * c3H17Node o (9 * m))⌉ : ℚ) / 10 ^ 8 +
        (⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o) + 9 * c3H17Lip o))⌉ : ℚ) /
          10 ^ 8 := by
  unfold c3H17Table
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
  exact min_le_right _ _

/-- A rational that is at most every listed number is at most the table: together with the
`c3H17Table_le_*` lemmas, the table is the least of the listed numbers. -/
theorem le_c3H17Table {c o m : ℤ} {x : ℚ} (h₁ : x ≤ 1)
    (hp : 3 ≤ c → x ≤ 1 - c3NarrowDeficit c o)
    (hd : 3 ≤ c → x ≤ c3H17CapUp c ((m : ℚ) / 2 ^ o) +
      (⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o)))⌉ : ℚ) / 10 ^ 8)
    (hj : c ∉ ({4, 5} : Finset ℤ) → x ≤
      (⌈(10 ^ 8 : ℚ) * (c3H17CapUp c ((m : ℚ) / 2 ^ o) * c3H17Node o (9 * m))⌉ : ℚ) / 10 ^ 8 +
        (⌈(10 ^ 8 : ℚ) * ((10 ^ 6 : ℚ)⁻¹ * (trLipConst c * 2 ^ (-o) + 9 * c3H17Lip o))⌉ : ℚ) /
          10 ^ 8) :
    x ≤ c3H17Table c o m := by
  unfold c3H17Table
  refine le_min (le_min h₁ ?_) ?_
  · split
    · rename_i hc
      exact le_min (hp hc) (hd hc)
    · exact h₁
  · split
    · rename_i hc
      exact hj hc
    · exact h₁

end CollatzPosDens
