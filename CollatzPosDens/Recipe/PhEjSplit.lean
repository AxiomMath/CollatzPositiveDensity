/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhEj
public import CollatzPosDens.Recipe.PhEmx

/-!
# Splitting the propagation majorant

The propagation majorant `E_j` splits into its mixing part `E_j^mx` and two explicit error terms:
for every natural number `j`,
$$\mathsf E_j\le\mathsf E^{\mathrm{mx}}_j+2^{8}\,j^{5/2}\,\mathsf g^{-j}
  +2^{-20}\,j^{5/2}\bigl(\mathsf g^{1/2}\,2^{-1/56}\bigr)^j,$$
with positive real powers and `𝗀 = 101/100`.

Writing `x = 2 ^ 12 𝗀 ^ j`, the logarithmic term of `2 * mxProfile .b x`, built from
`fourierPrefactor .b`, `amix .b`, `bootU .b` and `bootV .b`, gives exactly `E_j^mx`, since
`x ^ (-a) = 2 ^ (-12 a) 𝗀 ^ (-a j)` and `log x = 12 log 2 + j log 𝗀`. The terms involving
`bootW = 15000000/164241` and `𝗀 ^ (-3j/2) / 2` contribute at most
`Hhist (bootW / 2 ^ 23 + 1/2) j ^ (5/2) 𝗀 ^ (-j)`, and
`Hhist (bootW / 2 ^ 23 + 1/2) = 154283033231/896974848 = 172.003… < 2 ^ 8`. The last term is
bounded using `Hhist = 344 ≤ 2 ^ 9`.

## Main results

* `CollatzPosDens.propagationMajorant_le_split`: the splitting bound for `E_j`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The propagation majorant splits into its mixing part and two explicit error terms:
`E_j ≤ E_j^mx + 2 ^ 8 j ^ (5/2) 𝗀 ^ (-j) + 2 ^ (-20) j ^ (5/2) (𝗀 ^ (1/2) 2 ^ (-1/56)) ^ j`,
with positive real powers. -/
@[collatz_pos_dens "lem_ph_Ej_split"]
theorem propagationMajorant_le_split (j : ℕ) :
    propagationMajorant j ≤
      propagationMixingMajorant j +
        2 ^ 8 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ (-(j : ℝ)) +
        (2 : ℝ) ^ (-20 : ℝ) * (j : ℝ) ^ (5 / 2 : ℝ) *
          ((growthRatio : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ))) ^ (j : ℝ) := by
  set G : ℝ := (growthRatio : ℝ) with hGdef
  set s : ℝ := (j : ℝ) with hs
  set a : ℝ := (amix .b : ℝ) with ha
  have hG : 0 < G := growthRatio_cast_pos
  have hG1 : 1 ≤ G := one_lt_growthRatio_cast.le
  have hs0 : 0 ≤ s := Nat.cast_nonneg j
  have hGs : 0 < G ^ s := Real.rpow_pos_of_pos hG _
  have hxa : ((2 : ℝ) ^ 12 * G ^ s) ^ (-a) = (2 : ℝ) ^ (-(12 * a)) * G ^ (-(a * s)) := by
    rw [Real.mul_rpow (by norm_num) hGs.le, ← Real.rpow_mul hG.le,
      show ((2 : ℝ) ^ 12) = (2 : ℝ) ^ (12 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    ring_nf
  have hx2 : ((2 : ℝ) ^ 12 * G ^ s) ^ (-2 : ℝ) = 1 / 2 ^ 24 * G ^ (-(2 * s)) := by
    rw [Real.mul_rpow (by norm_num) hGs.le, ← Real.rpow_mul hG.le,
      Real.rpow_neg (by norm_num), Real.rpow_two]
    ring_nf
  have hlog : Real.log ((2 : ℝ) ^ 12 * G ^ s) = 12 * Real.log 2 + s * Real.log G :=
    (twelve_mul_log_two_add_mul_log_growthRatio j).symm
  have h1 : G ^ (s / 2) * G ^ (-(a * s)) = G ^ (-((a - 1 / 2) * s)) := by
    rw [← Real.rpow_add hG]; ring_nf
  have h2 : G ^ (s / 2) * G ^ (-(2 * s)) ≤ G ^ (-s) := by
    rw [← Real.rpow_add hG]
    exact Real.rpow_le_rpow_of_exponent_le hG1 (by linarith)
  have h3 : G ^ (s / 2) * G ^ (-(3 * s / 2)) = G ^ (-s) := by
    rw [← Real.rpow_add hG]; ring_nf
  have h4 : G ^ (s / 2) * (2 : ℝ) ^ (-(s / 56)) =
      (G ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ))) ^ s := by
    rw [Real.mul_rpow (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg (by norm_num) _),
      ← Real.rpow_mul hG.le, ← Real.rpow_mul (by norm_num)]
    ring_nf
  have h20 : (2 : ℝ) ^ (-20 : ℝ) = 2 ^ 9 * (2 : ℝ) ^ (-29 : ℝ) := by
    rw [show (-20 : ℝ) = 9 + -29 by norm_num, Real.rpow_add two_pos]
    norm_num
  set J : ℝ := (j : ℝ) ^ (5 / 2 : ℝ) with hJ
  have hJ0 : 0 ≤ J := Real.rpow_nonneg hs0 _
  have hH : ((Hhist : ℚ) : ℝ) = 344 := Hhist_cast
  have hW : ((bootW : ℚ) : ℝ) = 15000000 / 164241 := by
    rw [bootW_val]; norm_num
  have hP : 0 ≤ (2 : ℝ) ^ (-29 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hQ : 0 ≤ (G ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ))) ^ s :=
    Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg (by norm_num) _)) _
  have hGm : 0 ≤ G ^ (-s) := Real.rpow_nonneg hG.le _
  rw [propagationMajorant_def, propagationMixingMajorant_def, mxProfile_b, hxa, hx2, hlog, hH,
    hW, h20]
  rw [← hs, ← hJ]
  have e2 : 0 ≤ J * (G ^ (-s) - G ^ (s / 2) * G ^ (-(2 * s))) :=
    mul_nonneg hJ0 (by linarith)
  have e3 : 0 ≤ J * G ^ (-s) := mul_nonneg hJ0 hGm
  have e4 : 0 ≤ J * ((2 : ℝ) ^ (-29 : ℝ) * (G ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (-(1 / 56 : ℝ))) ^ s) :=
    mul_nonneg hJ0 (mul_nonneg hP hQ)
  have key :
      344 * J * G ^ (s / 2) *
          (2 * (18 * fourierPrefactor .b * ((2 : ℝ) ^ (-(12 * a)) * G ^ (-(a * s))) *
                (bootU .b * (12 * Real.log 2 + s * Real.log G) + bootV .b) +
                15000000 / 164241 * (1 / 2 ^ 24 * G ^ (-(2 * s)))) +
            1 / 2 * G ^ (-(3 * s / 2)) + (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-(s / 56))) =
        36 * 344 * fourierPrefactor .b * (2 : ℝ) ^ (-(12 * a)) * J *
            (G ^ (s / 2) * G ^ (-(a * s))) *
            (bootU .b * (12 * Real.log 2 + s * Real.log G) + bootV .b) +
          344 * J * (2 * (15000000 / 164241) / 2 ^ 24 *
              (G ^ (s / 2) * G ^ (-(2 * s))) +
            1 / 2 * (G ^ (s / 2) * G ^ (-(3 * s / 2)))) +
          344 * J * ((2 : ℝ) ^ (-29 : ℝ) * (G ^ (s / 2) * (2 : ℝ) ^ (-(s / 56)))) := by
    ring
  rw [key, h1, h3, h4]
  linear_combination (344 * (2 * (15000000 / 164241) / 2 ^ 24) : ℝ) * e2 +
    (2 ^ 8 - 344 * (2 * (15000000 / 164241) / 2 ^ 24 + 1 / 2) : ℝ) * e3 +
    (2 ^ 9 - 344 : ℝ) * e4

end CollatzPosDens
