/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.FirstCrossing.FcMgf
public import CollatzPosDens.Transfer.Concentration

/-!
# Lower tail for valuation sums

Under the geometric mass `𝐩`, the letters of a word `x ∈ ℤ_{≥1}^H` behave like independent
geometric variables of mean `2`. This file proves the Chernoff lower-tail bound: for an integer
`H ≥ 1` and a real `v > 0` with `4v/(9H) ≤ 1/32`,
`𝐩({x ∈ ℤ_{≥1}^H : A(x) - 2H ≤ -v}) ≤ exp(-2v²/(9H))`.

With `t = 4v/(9H)`, on the set in question `1 ≤ e^{-t(A(x) - 2H) - tv}`, so its mass is at most
`e^{-tv} ∑_x 2^{-A(x)} e^{-t(A(x) - 2H)} = e^{-tv} φ(-t)^H`, where
`φ(s) = ∑_{a ≥ 1} 2^{-a} e^{s(a-2)}`; the bound `φ(-t) ≤ e^{9t²/8}` then gives
`exp(-tv + 9Ht²/8) = exp(-2v²/(9H))`.

## Main results

* `CollatzPosDens.fcLowerTail_tsum_tilt`: the tilted total mass
  `∑_{|x| = H} 2^{-A(x)} e^{s(A(x) - 2H)} = φ(s)^H`.
* `CollatzPosDens.fcLowerTail_geomMass_le`: the lower-tail bound.

## Implementation notes

Words of length `H` stand for `ℤ_{≥1}^H`. The sums are taken in `ℝ≥0∞`, so Tonelli's theorem
is the unconditional `ENNReal.tsum_prod`; the factorisation over the letters is
`tsum_massWeight_mul_exp_valSum` and `φ` is `concentrationMgf` (`concentrationMgf_eq_ofReal`
gives it as a real series). The bound is stated with the right-hand side
`ENNReal.ofReal (exp (-2v²/(9H)))`, the real number `exp(-2v²/(9H))` viewed in `ℝ≥0∞`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- The `s`-tilted weight `2^{-A(x)} e^{s(A(x) - 2|x|)}` of a word, in `ℝ≥0∞`. -/
noncomputable abbrev fcLowerTailTilt (s : ℝ) (x : Word) : ℝ≥0∞ :=
  2⁻¹ ^ x.valSum * ENNReal.ofReal (exp (s * ((x.valSum : ℝ) - 2 * x.length)))

/-- **Tilted total mass.** For `e^s < 2`,
`∑_{|x| = H} 2^{-A(x)} e^{s(A(x) - 2H)} = φ(s)^H` with `φ(s) = ∑_{a ≥ 1} 2^{-a} e^{s(a-2)}`. -/
theorem fcLowerTail_tsum_tilt {s : ℝ} (hs : exp s < 2) (H : ℕ) :
    ∑' x : {x : Word | x.length = H}, fcLowerTailTilt s x =
      ENNReal.ofReal
        (∑' a : ℕ, (1 / 2 : ℝ) ^ (a + 1) * exp (s * (((a + 1 : ℕ) : ℝ) - 2))) ^ H := by
  rw [← concentrationMgf_eq_ofReal hs, ← tsum_massWeight_mul_exp_valSum]
  refine tsum_congr fun ⟨x, hx⟩ => ?_
  simp only [fcLowerTailTilt, Word.massWeight, show x.length = H from hx]

/-- **Lower tail for valuation sums.** For an integer `H ≥ 1` and a real `v > 0` with
`4v/(9H) ≤ 1/32`, `𝐩({x ∈ ℤ_{≥1}^H : A(x) - 2H ≤ -v}) ≤ exp(-2v²/(9H))`. -/
@[collatz_pos_dens "lem_fc_lower_tail"]
theorem fcLowerTail_geomMass_le {H : ℕ} (hH : 1 ≤ H) {v : ℝ} (hv : 0 < v)
    (hvH : 4 * v / (9 * H) ≤ 1 / 32) :
    geomMass {x : Word | x.length = H ∧ (x.valSum : ℝ) - 2 * H ≤ -v} ≤
      ENNReal.ofReal (exp (-2 * v ^ 2 / (9 * H))) := by
  set t := 4 * v / (9 * H) with ht
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have htpos : 0 < t := by positivity
  have habs : |-t| ≤ 1 / 32 := by rw [abs_neg, abs_of_pos htpos]; exact hvH
  have hexp : exp (-t) < 2 := by
    have := exp_le_one_iff.mpr (neg_nonpos.mpr htpos.le)
    linarith
  set φ := ∑' a : ℕ, (1 / 2 : ℝ) ^ (a + 1) * exp (-t * (((a + 1 : ℕ) : ℝ) - 2)) with hφ
  have hφb := fcMgf_bounds habs
  have hφ0 : 0 ≤ φ := by linarith [hφb.1]
  have hpt : ∀ x : {x : Word | x.length = H ∧ (x.valSum : ℝ) - 2 * H ≤ -v},
      (x : Word).massWeight ≤
        ENNReal.ofReal (exp (-t * v)) * fcLowerTailTilt (-t) x := by
    rintro ⟨x, hxl, hxv⟩
    simp only [Word.massWeight, fcLowerTailTilt, hxl]
    rw [mul_left_comm, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
    have : 1 ≤ exp (-t * v + -t * ((x.valSum : ℝ) - 2 * H)) := by
      apply one_le_exp
      nlinarith
    calc (2⁻¹ : ℝ≥0∞) ^ x.valSum = 2⁻¹ ^ x.valSum * 1 := (mul_one _).symm
      _ ≤ 2⁻¹ ^ x.valSum *
          ENNReal.ofReal (exp (-t * v + -t * ((x.valSum : ℝ) - 2 * H))) := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal this
  calc geomMass {x : Word | x.length = H ∧ (x.valSum : ℝ) - 2 * H ≤ -v}
      ≤ ∑' x : {x : Word | x.length = H ∧ (x.valSum : ℝ) - 2 * H ≤ -v},
          ENNReal.ofReal (exp (-t * v)) * fcLowerTailTilt (-t) x :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (exp (-t * v)) *
          ∑' x : {x : Word | x.length = H ∧ (x.valSum : ℝ) - 2 * H ≤ -v},
            fcLowerTailTilt (-t) x := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (exp (-t * v)) *
          ∑' x : {x : Word | x.length = H}, fcLowerTailTilt (-t) x := by
        gcongr 1
        exact ENNReal.tsum_mono_subtype _ fun x hx => hx.1
    _ = ENNReal.ofReal (exp (-t * v)) * ENNReal.ofReal φ ^ H := by
        rw [fcLowerTail_tsum_tilt hexp]
    _ = ENNReal.ofReal (exp (-t * v) * φ ^ H) := by
        rw [ENNReal.ofReal_mul (exp_pos _).le, ENNReal.ofReal_pow hφ0]
    _ ≤ ENNReal.ofReal (exp (-t * v) * exp (9 * (-t) ^ 2 / 8) ^ H) := by
        gcongr
        exact hφb.2
    _ = ENNReal.ofReal (exp (-2 * v ^ 2 / (9 * H))) := by
        congr 1
        rw [← exp_nat_mul, ← exp_add]
        congr 1
        rw [ht]
        field_simp
        ring

end CollatzPosDens
