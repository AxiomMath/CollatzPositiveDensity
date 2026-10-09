/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Mixing.MxHeadMass
public import CollatzPosDens.Mixing.MxSubmassTotal
public import CollatzPosDens.Mixing.MxHeadPointwise

/-!
# Collision bound for the head mass

Let `n ≥ 1` and `k, l ∈ ℕ`. Then
$$\sum_{y \in G_n} \mathrm{Hm}_{n,k,l}(y)^2 \le 2^{-l}\,\mathbf{p}(\mathrm{Hd}(n,k,l)).$$

The head mass is the submass `Sub^n_{Hd(n,k,l)}`, and submasses sum to the geometric mass, so
`∑_y Hm_{n,k,l}(y) = 𝐩(Hd(n, k, l))`. Since `0 ≤ Hm_{n,k,l}(y) ≤ 2^{-l}`, each
square satisfies `Hm_{n,k,l}(y)^2 ≤ 2^{-l} Hm_{n,k,l}(y)`, and summing over `y` gives the bound.

## Main results

* `CollatzPosDens.sum_mxHeadMass_eq_toReal_geomMass`:
  `∑_y Hm_{n,k,l}(y) = 𝐩(Hd(n, k, l))`.
* `CollatzPosDens.sum_mxHeadMass_sq_le_geomMass`:
  `∑_y Hm_{n,k,l}(y)^2 ≤ 2^{-l} 𝐩(Hd(n, k, l))`.

## Implementation notes

The head mass is real-valued while the geometric mass takes values in `[0, ∞]`; since the head
gate is finite, its geometric mass is finite and is compared through `ENNReal.toReal`. The
weight `2^{-l}` is written `2⁻¹ ^ l`. The hypothesis `n ≥ 1` is not used by the argument, so
the results are stated for every natural number `n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.6.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The head masses sum to the geometric mass of the head gate:
`∑_{y ∈ G_n} Hm_{n,k,l}(y) = 𝐩(Hd(n, k, l))`. -/
theorem sum_mxHeadMass_eq_toReal_geomMass (n k l : ℕ) :
    ∑ y, mxHeadMass n k l y = (geomMass (mxHeadGate n k l)).toReal := by
  have h y : mxHeadMass n k l y = (subMass n (mxHeadGate n k l) y).toReal := by
    rw [← ofReal_mxHeadMass, ENNReal.toReal_ofReal (mxHeadMass_nonneg n k l y)]
  simp_rw [h]
  rw [← ENNReal.toReal_sum fun y _ => ofReal_mxHeadMass n k l y ▸ ENNReal.ofReal_ne_top,
    sum_subMass]

/-- **Collision bound for the head mass.** For all `n, k, l ∈ ℕ`,
`∑_{y ∈ G_n} Hm_{n,k,l}(y)^2 ≤ 2^{-l} 𝐩(Hd(n, k, l))`. -/
@[collatz_pos_dens "lem_mx_head_collision"]
theorem sum_mxHeadMass_sq_le_geomMass (n k l : ℕ) :
    ∑ y, mxHeadMass n k l y ^ 2 ≤ (2⁻¹ : ℝ) ^ l * (geomMass (mxHeadGate n k l)).toReal :=
  calc ∑ y, mxHeadMass n k l y ^ 2 ≤ ∑ y, (2⁻¹ : ℝ) ^ l * mxHeadMass n k l y :=
        Finset.sum_le_sum fun y _ => by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (mxHeadMass_le_two_inv_pow n k l y)
            (mxHeadMass_nonneg n k l y)
    _ = (2⁻¹ : ℝ) ^ l * (geomMass (mxHeadGate n k l)).toReal := by
        rw [← Finset.mul_sum, sum_mxHeadMass_eq_toReal_geomMass]

end CollatzPosDens
