/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3PaidPassage
public import CollatzPosDens.StoppingTrace.TrGapNonneg
public import CollatzPosDens.StoppingTrace.TrPassageLaw

/-!
# The paid passage mass is dominated by the first-passage law

Fix a level `n` and a residue `ξ ∈ G_n`, and let the gap refer to `(n, ξ, ε_*)`. For a point
`e` with gap `ω = gap(e)` and a lattice point `x`, the paid passage mass satisfies
`0 ≤ F̃_e(x) ≤ F_ω(x)`, where `F_ω` is the first-passage law of level `ω`.

Every reward is nonnegative, so the weighted white count `N^*` is nonnegative and each discount
factor `exp(-z_* N^*)` lies in `(0, 1]`. Dropping the discounts bounds `F̃_e(x)` by the total
weight `∑_{π ∈ Π_ω} bw^⊗(π) [Bp_{|π|}(π) = x]` of the passage lists ending at `x`, which is
`F_ω(x)` because the passage lists carry the first-passage law.

## Main results

* `CollatzPosDens.c3PaidPassage_le_firstPassageLaw`: `0 ≤ F̃_e(x) ≤ F_ω(x)` with `ω = gap(e)`.

## Implementation notes

The bound is stated for every `e : ℤ × ℤ`, not only for black points `e ∈ 𝒫`: the gap is
nonnegative for every point (`CollatzPosDens.trGap_nonneg`), so indexing the passage set `Π_ω` by
`Int.toNat ω` loses nothing. The mass `F̃_e(x)` lives in `[0, ∞]` and the real number `F_ω(x)`
enters through `ENNReal.ofReal`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- **The paid passage mass is dominated by the first-passage law.** For every point `e` with
gap `ω = gap(e)` (for `(n, ξ, ε_*)`) and every `x ∈ ℤ × ℤ`, `0 ≤ F̃_e(x) ≤ F_ω(x)`. -/
@[collatz_pos_dens "lem_c3_paid_dom"]
theorem c3PaidPassage_le_firstPassageLaw (n : ℕ) (ξ : ResidueGroup n) (e x : ℤ × ℤ) :
    0 ≤ c3PaidPassage n ξ e x ∧
      c3PaidPassage n ξ e x ≤
        ENNReal.ofReal (firstPassageLaw (trGap n ξ (epsStar : ℝ) e) x) := by
  refine ⟨zero_le, ?_⟩
  set ω := trGap n ξ (epsStar : ℝ) e
  have hω : ((ω.toNat : ℕ) : ℤ) = ω := Int.toNat_of_nonneg (trGap_nonneg _ _ _ _)
  let G : ℤ × ℤ → ℝ≥0∞ := fun y => if y = x then 1 else 0
  calc c3PaidPassage n ξ e x
      ≤ ∑' π : trPassage ω.toNat,
          ENNReal.ofReal (trListWeight π.1) * G (chBlockPath π.1 π.1.length) := by
        refine ENNReal.tsum_le_tsum fun π => ?_
        by_cases h : chBlockPath π.1 π.1.length = x
        · simp only [h, G, ite_true, mul_one]
          refine ENNReal.ofReal_le_ofReal ?_
          refine mul_le_of_le_one_right (trListWeight_nonneg _) (Real.exp_le_one_iff.mpr ?_)
          have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
          nlinarith [trCount_nonneg (n := n) (ξ := ξ) e π.1 π.1.length]
        · simp [h, G]
    _ = ∑' y : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw (ω.toNat : ℤ) y) * G y :=
        tsum_trPassage_eq_tsum_firstPassageLaw _ G
    _ = ENNReal.ofReal (firstPassageLaw ω x) := by
        rw [tsum_eq_single x fun y hy => by simp [G, hy], hω]
        simp [G]

end CollatzPosDens
