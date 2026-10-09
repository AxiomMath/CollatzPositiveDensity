/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.Reduction
public import CollatzPosDens.Mixing.MxLargeScale
public import CollatzPosDens.Mixing.MxOscForm

/-!
# The mixing lemma

For integers `2 ^ 131072 ≤ m ≤ q`, the reference density `ρ_q` is close on average to the
pulled-back coarser density `ρ_m ∘ π_{q,m}`:
$$\langle |\rho_q - \rho_m \circ \pi_{q,m}| \rangle_q \le \frac{2C}{3m^{9/8}},$$
where `C = 477/20 · X_*^{A_*} + 159/10` is the mixing coefficient `mixingConst`. It follows by
combining the oscillation form `⟨|ρ_q - ρ_m ∘ π_{q,m}|⟩_q = (2/3) Osc_{m,q}(μ_q)` with the
large-scale oscillation bound `Osc_{m,q}(μ_q) ≤ C m^{-9/8}`.

## Main results

* `CollatzPosDens.residueAvg_abs_refDensity_sub_le_of_two_pow_le`: the bound above.

## Implementation notes

The power `m^{9/8}` is the real power `Real.rpow`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Mixing lemma.** For integers `2 ^ 131072 ≤ m ≤ q`,
`⟨|ρ_q - ρ_m ∘ π_{q,m}|⟩_q ≤ 2C / (3 m^{9/8})`, where `C` is the mixing coefficient. -/
@[collatz_pos_dens "lem_mixing"]
theorem residueAvg_abs_refDensity_sub_le_of_two_pow_le {m q : ℕ} (hm : 2 ^ 131072 ≤ m)
    (h : m ≤ q) :
    residueAvg q (fun y => |refDensity q y - refDensity m (residueReduction h y)|) ≤
      2 * mixingConst / (3 * (m : ℝ) ^ (9 / 8 : ℝ)) := by
  rw [residueAvg_abs_refDensity_sub h]
  calc 2 / 3 * oscillation h (fun y => (refLaw q y).toReal)
      ≤ 2 / 3 * (mixingConst * (m : ℝ) ^ (-(9 / 8 : ℝ))) :=
        mul_le_mul_of_nonneg_left (oscillation_refLaw_le_mixingConst_of_two_pow_le hm h)
          (by norm_num)
    _ = 2 * mixingConst / (3 * (m : ℝ) ^ (9 / 8 : ℝ)) := by
        rw [Real.rpow_neg (Nat.cast_nonneg m)]
        field_simp

end CollatzPosDens
