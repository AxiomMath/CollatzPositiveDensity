/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Renewal.RnHoldJmarginal

/-!
# Horizontal moment generating function of hold lists

For `N ∈ ℕ` and real `t`, the sum in `[0, ∞]` of the series of nonnegative terms
`∑_{h ∈ 𝒫^N} η^{⊗N}(h) e^{t (j(h_1) + ⋯ + j(h_N))}` equals `M₄₅(t)^N`. The summand factorises
over the coordinates, so by Tonelli the sum is the `N`-th power of the one-step sum
`∑_{(j, l) ∈ 𝒫} η(j, l) e^{t j}`, and this equals `∑_{j ≥ 1} ν₄₅(j) e^{t j} = M₄₅(t)` by the
`j`-marginal of `η`.

## Main results

* `CollatzPosDens.tsum_holdLaw_mul_exp`: `∑_{(j, l) ∈ 𝒫} η(j, l) e^{t j} = M₄₅(t)`.
* `CollatzPosDens.tsum_holdListLaw_mul_exp`: the series over `𝒫^N` sums to `M₄₅(t)^N`.
* `CollatzPosDens.tsum_holdListLaw_mul_exp_pi`: the same identity with `𝒫^N` written as
  the tuples `Fin N → 𝒫`.

## Implementation notes

As in `CollatzPosDens.holdListLaw`, a point is a pair `(j, l) : ℕ × ℤ`, and `𝒫 = ℤ_{≥1} × ℤ` is
the set of pairs with `1 ≤ j`. The restriction `1 ≤ j` matters: at `j = 0` the law `η(0, l)` is
the indicator of `l = 0`, not zero. Accordingly `𝒫^N` is the set of `h : Fin N → ℕ × ℤ` all of
whose entries have `1 ≤ j(h_i)`. All sums are taken in `ℝ≥0∞`, each term being embedded by
`ENNReal.ofReal`, so no hypothesis on `t` is needed; `M₄₅(t)` may be `∞`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- **One-step horizontal moment.** For real `t`,
`∑_{(j, l) ∈ 𝒫} η(j, l) e^{t j} = M₄₅(t)` in `[0, ∞]`. -/
theorem tsum_holdLaw_mul_exp (t : ℝ) :
    ∑' p : {p : ℕ × ℤ // 1 ≤ p.1},
      ENNReal.ofReal (holdLaw p.1.1 p.1.2 * exp (t * p.1.1)) = mgfNu45 t := by
  rw [← natPointsEquiv.tsum_eq, mgfNu45_def, ENNReal.tsum_prod']
  refine tsum_congr fun n ↦ ?_
  have h := (hasSum_holdLaw (j := n + 1) (by omega)).mul_right (exp (t * ((n : ℝ) + 1)))
  simp only [natPointsEquiv, Equiv.coe_fn_mk, Nat.cast_add, Nat.cast_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun _ ↦ mul_nonneg (holdLaw_nonneg _ _) (exp_pos _).le) h.summable, h.tsum_eq]
  push_cast
  rfl

/-- **Horizontal moment generating function of hold lists**, with `𝒫^N` written as tuples
`Fin N → 𝒫`: for `N ∈ ℕ` and real `t`,
`∑_{h ∈ 𝒫^N} η^{⊗N}(h) e^{t (j(h_1) + ⋯ + j(h_N))} = M₄₅(t)^N` in `[0, ∞]`. -/
theorem tsum_holdListLaw_mul_exp_pi (N : ℕ) (t : ℝ) :
    ∑' h : Fin N → {p : ℕ × ℤ // 1 ≤ p.1},
      ENNReal.ofReal (holdListLaw (fun i ↦ (h i).1) * exp (t * ∑ i, ((h i).1.1 : ℝ))) =
      mgfNu45 t ^ N := by
  rw [← tsum_holdLaw_mul_exp, ← tsum_pi_fin_prod_ennreal_const]
  refine tsum_congr fun h ↦ ?_
  rw [holdListLaw_def, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib,
    ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ mul_nonneg (holdLaw_nonneg _ _) (exp_pos _).le]

/-- **Horizontal moment generating function of hold lists.** For `N ∈ ℕ` and real `t`, the sum
in `[0, ∞]` of the series of nonnegative terms
`∑_{h ∈ 𝒫^N} η^{⊗N}(h) e^{t (j(h_1) + ⋯ + j(h_N))}` equals `M₄₅(t)^N` (which is `1` for
`N = 0`). Here `𝒫^N` is the set of `h : Fin N → ℕ × ℤ` with `1 ≤ j(h_i)` for every `i`. -/
@[collatz_pos_dens "lem_rn_list_hor_mgf"]
theorem tsum_holdListLaw_mul_exp (N : ℕ) (t : ℝ) :
    ∑' h : {h : Fin N → ℕ × ℤ // ∀ i, 1 ≤ (h i).1},
      ENNReal.ofReal (holdListLaw h.1 * exp (t * ∑ i, ((h.1 i).1 : ℝ))) = mgfNu45 t ^ N := by
  rw [← tsum_holdListLaw_mul_exp_pi]
  exact (Equiv.subtypePiEquivPi (α := Fin N) (p := fun _ (p : ℕ × ℤ) ↦ 1 ≤ p.1)).tsum_eq
    (fun h ↦ ENNReal.ofReal (holdListLaw (fun i ↦ (h i).1) * exp (t * ∑ i, ((h i).1.1 : ℝ))))

end CollatzPosDens
