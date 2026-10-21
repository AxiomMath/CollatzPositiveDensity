/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05OfflawCdf
public import CollatzPosDens.Seed.S05OfflawRecursion
public import CollatzPosDens.Seed.S05OfflawSubfix
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Mixing.MxOffsetTail

/-!
# A certificate is below the offset law

Let `g` be an offset-law certificate (`CollatzPosDens.IsOfflawCert`) and `Ĝ = Ĝ_g` its step
function (`CollatzPosDens.offlawStep`). Then for every `D ∈ ℕ` and every real `x`,
$$\widehat{\mathsf G}_g(x) \le \mathsf F_D(x),$$
where `𝖥_D` is the offset distribution function `CollatzPosDens.offlawCdf`.

The proof is by induction on `D`. Both sides vanish for `x < 0`, and `Ĝ ≤ 1 = 𝖥₀` on `[0, ∞)`.
For the step, the tail bound `𝐩({off ≥ x}) ≤ 7/(x + 2)` and the total mass `1` of
`ℤ_{≥1}^{D+1}` give `𝖦₀(x) ≤ 𝖥_{D+1}(x)`; the induction hypothesis and the recursion
`𝖥_{D+1}(x) = ∑_{a ≥ 1} 2^{-a} 𝖥_D((2^a x - 1)/3)` bound the series
`∑_{a ≥ 1} 2^{-a} Ĝ((2^a x - 1)/3)` by `𝖥_{D+1}(x)`; and the sub-fixed-point inequality
`Ĝ(x) ≤ max(𝖦₀(x), ∑_{a ≥ 1} 2^{-a} Ĝ((2^a x - 1)/3))` concludes.

## Main results

* `CollatzPosDens.offlawFloor_le_offlawCdf`: `𝖦₀(x) ≤ 𝖥_D(x)` for every `D` and `x ≥ 0`.
* `CollatzPosDens.IsOfflawCert.offlawStep_le_offlawCdf`: `Ĝ_g(x) ≤ 𝖥_D(x)` for every `D` and
  every real `x`.

## Implementation notes

The step function is real-valued and the distribution function takes values in `[0, ∞]`; the
comparison is stated through `ENNReal.ofReal`, which is faithful since `Ĝ_g ≥ 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The tail floor is below the offset distribution function: `𝖦₀(x) ≤ 𝖥_D(x)` for every
`D ∈ ℕ` and real `x ≥ 0`. -/
theorem offlawFloor_le_offlawCdf (D : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (offlawFloor x) ≤ offlawCdf D x := by
  have htot : offlawCdf D x + geomMass {u : Word | u.length = D ∧ x < (off u : ℝ)} = 1 := by
    rw [offlawCdf_def, ← geomMass_union, ← geomMass_setOf_length_eq D]
    · congr 1
      ext u
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        rcases le_or_gt (off u : ℝ) x with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
    · rw [Set.disjoint_left]
      rintro u ⟨-, h1⟩ ⟨-, h2⟩
      exact absurd h1 (not_le.2 h2)
  have htail : geomMass {u : Word | u.length = D ∧ x < (off u : ℝ)} ≤
      ENNReal.ofReal (7 / (x + 2)) :=
    (geomMass_mono fun u (hu : u.length = D ∧ x < (off u : ℝ)) =>
      show u.length = D ∧ x ≤ (off u : ℝ) from ⟨hu.1, hu.2.le⟩).trans
      (geomMass_offsetTail_le D hx)
  have h1 : 1 ≤ offlawCdf D x + ENNReal.ofReal (7 / (x + 2)) :=
    htot.symm.le.trans (add_le_add_right htail _)
  rw [offlawFloor, ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_max,
    ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  exact tsub_le_iff_right.2 h1

namespace IsOfflawCert

variable {g : Fin 6199 → ℕ}

/-- **A certificate is below the offset law**: if `g` is an offset-law certificate, then
`Ĝ_g(x) ≤ 𝖥_D(x)` for every `D ∈ ℕ` and every real `x`. -/
@[collatz_pos_dens "lem_s05_offlaw_below"]
theorem offlawStep_le_offlawCdf (hg : IsOfflawCert g) (D : ℕ) (x : ℝ) :
    ENNReal.ofReal (offlawStep g x) ≤ offlawCdf D x := by
  induction D generalizing x with
  | zero =>
    rw [offlawCdf_zero]
    split_ifs with hx
    · exact ENNReal.ofReal_le_one.2 (hg.offlawStep_le_one x)
    · rw [offlawStep_of_neg g (not_le.1 hx), ENNReal.ofReal_zero]
  | succ D ih =>
    rcases lt_or_ge x 0 with hx | hx
    · rw [offlawStep_of_neg g hx, ENNReal.ofReal_zero]
      exact bot_le
    refine (ENNReal.ofReal_le_ofReal (hg.offlawStep_le_max hx)).trans ?_
    rw [ENNReal.ofReal_max]
    refine max_le (offlawFloor_le_offlawCdf (D + 1) hx) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun a => mul_nonneg (by positivity) (offlawStep_nonneg g _))
      (hg.summable_offlawStep x), offlawCdf_succ]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    gcongr; exact ih _

end IsOfflawCert

end CollatzPosDens
