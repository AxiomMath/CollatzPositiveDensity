/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05JointCert
public import CollatzPosDens.Seed.S05JointRecursion
public import CollatzPosDens.Seed.S05OfflawBelow
public import CollatzPosDens.Seed.S05OfflawStep

/-!
# A joint certificate is below the joint offset law

Let `g` be an offset-law certificate (`CollatzPosDens.IsOfflawCert`) and `𝖸` a joint
certificate over `g` (`CollatzPosDens.IsJointCert`). Then
$$2^{-62}\,\mathsf Y_q(r, k) \le \mathsf F^{\mathrm{jt}}_{D,q}(r, \xi_k)$$
for all integers `1 ≤ q ≤ 8`, `D ≥ q`, `0 ≤ k ≤ 6198` and every `r ∈ G_q`.

At the level `q = 0` the joint offset law is the offset distribution function `𝖥_D`, since
`G_0` is trivial; the certificate bound `Ĝ_g ≤ 𝖥_D` and `⌊z⌋ ≤ z` then give
`2^{-62} c_g(k,a) ≤ 2^{-a} 𝖥_D(y_{k,a})` with `y_{k,a} = (2^a ξ_k - 1)/3`. For `q ≥ 1` one
shows, letter by letter, that `2^{-62} c^{jt}_{g,𝖸}(q, r, k, a)` is at most the term of index
`a` of the one-letter recursion of `𝖥^{jt}_{D,q}(r, ξ_k)`: by the level-zero bound for `q = 1`,
and for `q ≥ 2` by induction on `q` at the grid index `ι(y_{k,a})`, since `ξ_{ι(y)} ≤ y` and the
joint offset law is nondecreasing. Summing over `1 ≤ a ≤ 60` and dropping the nonnegative terms
with `a > 60` concludes.

## Main results

* `CollatzPosDens.jointLaw_zero`: `𝖥^{jt}_{D,0}(r, x) = 𝖥_D(x)`.
* `CollatzPosDens.IsJointCert.div_le_jointLaw`: the bound
  `2^{-62} 𝖸_q(r, k) ≤ 𝖥^{jt}_{D,q}(r, ξ_k)`.

## Implementation notes

The joint offset law takes values in `[0, ∞]`, and the bound is stated there, with
`2^{-62} 𝖸_q(r, k)` written `𝖸_q(r, k) / 2^62`. The grid index ranges over `Fin 6199`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open Finset

namespace CollatzPosDens

/-- At the level `q = 0` the joint offset law is the offset distribution function:
`𝖥^{jt}_{D,0}(r, x) = 𝖥_D(x)`, since `G_0` has a single element. -/
theorem jointLaw_zero (D : ℕ) (r : ResidueGroup 0) (x : ℝ) :
    jointLaw D 0 r x = offlawCdf D x := by
  rw [jointLaw_def, offlawCdf_def]
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq, @Subsingleton.elim (ZMod 1) _ (prefixResidue 0 u) r, and_true]

/-- If `n ≤ 2^{-a} 2^62 t` and `t ≤ X`, then `n / 2^62 ≤ 2^{-a} X` in `[0, ∞]`. -/
private theorem jointBelow_natCast_div_le {n a : ℕ} {t : ℝ} {X : ℝ≥0∞}
    (hn : (n : ℝ) ≤ ((2 : ℝ) ^ a)⁻¹ * (2 ^ 62 * t)) (hX : ENNReal.ofReal t ≤ X) :
    (n : ℝ≥0∞) / 2 ^ 62 ≤ 2⁻¹ ^ a * X := by
  have h1 : (n : ℝ≥0∞) / 2 ^ 62 = ENNReal.ofReal ((n : ℝ) / 2 ^ 62) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have h2 : (2⁻¹ : ℝ≥0∞) ^ a = ENNReal.ofReal ((2 : ℝ) ^ a)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  have hle : (n : ℝ) / 2 ^ 62 ≤ ((2 : ℝ) ^ a)⁻¹ * t := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  rw [h1, h2]
  calc ENNReal.ofReal ((n : ℝ) / 2 ^ 62) ≤ ENNReal.ofReal (((2 : ℝ) ^ a)⁻¹ * t) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((2 : ℝ) ^ a)⁻¹ * ENNReal.ofReal t :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by gcongr

/-- **Level zero.** For an offset-law certificate `g`, every `D ∈ ℕ`, `0 ≤ k ≤ 6198` and every
`a`, `2^{-62} c_g(k,a) ≤ 2^{-a} 𝖥_D(y_{k,a})` with `y_{k,a} = (2^a ξ_k - 1)/3`. -/
theorem IsOfflawCert.offlawContrib_div_le_offlawCdf {g : Fin 6199 → ℕ} (hg : IsOfflawCert g)
    (D : ℕ) (k : Fin 6199) (a : ℕ) :
    (offlawContrib g k a : ℝ≥0∞) / 2 ^ 62 ≤
      2⁻¹ ^ a * offlawCdf D (((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3) := by
  set y : ℝ := ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 with hy_def
  rcases lt_or_ge y 0 with hy | hy0
  · rw [offlawContrib_of_neg g hy]
    simp
  refine jointBelow_natCast_div_le ?_ (hg.offlawStep_le_offlawCdf D y)
  rcases lt_or_ge ((offlawGrid 6198 : ℚ) : ℝ) y with hy1 | hy1
  · rw [offlawContrib_of_lt g hy1, offlawStep_of_gt g hy1]
    have hG := offlawFloor_nonneg y
    refine (Nat.floor_le (by positivity)).trans ?_
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by positivity)
  · rw [offlawContrib_of_nonneg_of_le g hy0 hy1, offlawStep_of_mem_Icc g hy0 hy1]
    refine (Nat.floor_le (by positivity)).trans (le_of_eq ?_)
    rw [offlawIndexFin]
    field_simp
    rfl

/-- A finite sum over the letters `1 ≤ a ≤ 60` is at most the sum over all letters `a ≥ 1`. -/
private theorem jointBelow_sum_Icc_le_tsum (F : ℕ → ℝ≥0∞) :
    ∑ a ∈ Icc 1 60, F a ≤ ∑' a : ℕ+, F a := by
  rw [tsum_pnat_eq_tsum_succ, show Icc 1 60 = Ico 1 61 from rfl, Finset.sum_Ico_eq_sum_range]
  simp only [show 61 - 1 = 60 from rfl, add_comm 1]
  exact ENNReal.sum_le_tsum _

/-- **A joint certificate is below the joint offset law.** If `g` is an offset-law certificate
and `𝖸` a joint certificate over `g`, then `2^{-62} 𝖸_q(r, k) ≤ 𝖥^{jt}_{D,q}(r, ξ_k)` for all
`1 ≤ q ≤ 8`, `D ≥ q`, `0 ≤ k ≤ 6198` and `r ∈ G_q`. -/
@[collatz_pos_dens "lem_s05_joint_below"]
theorem IsJointCert.div_le_jointLaw {g : Fin 6199 → ℕ}
    {Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ} (hg : IsOfflawCert g) (hY : IsJointCert g Y)
    {q D : ℕ} (hq : 1 ≤ q) (hq8 : q ≤ 8) (hD : q ≤ D) (k : Fin 6199) (r : ResidueGroup q) :
    (Y q r k : ℝ≥0∞) / 2 ^ 62 ≤ jointLaw D q r ((offlawGrid k : ℚ) : ℝ) := by
  induction q generalizing D k with
  | zero => omega
  | succ q ih =>
    set x : ℝ := ((offlawGrid k : ℚ) : ℝ) with hx_def
    set T : ℕ → ℝ≥0∞ := fun a => if (3 : ℤ) ∣ 2 ^ a * (r.val : ℤ) - 1 then
        (2⁻¹ : ℝ≥0∞) ^ a * jointLaw (D - 1) (q + 1 - 1) (childResidue a r)
          ((2 ^ a * x - 1) / 3)
      else 0 with hT_def
    have hdag : ∀ a, (jointContrib g Y (q + 1) r k a : ℝ≥0∞) / 2 ^ 62 ≤ T a := by
      intro a
      by_cases hdvd : (3 : ℤ) ∣ 2 ^ a * (r.val : ℤ) - 1
      swap
      · rw [jointContrib_of_not_dvd g Y r k hdvd]
        simp
      simp only [hT_def, hdvd, ↓reduceIte]
      rcases Nat.eq_zero_or_pos q with rfl | hq0
      · rw [jointContrib_one g Y r k hdvd, jointLaw_zero]
        exact hg.offlawContrib_div_le_offlawCdf (D - 1) k a
      have hq1 : q + 1 ≠ 1 := by omega
      set y : ℝ := ((2 : ℝ) ^ a * x - 1) / 3 with hy_def
      rcases lt_or_ge y 0 with hy | hy0
      · rw [jointContrib_of_neg g Y r hq1 hy]
        simp
      rcases lt_or_ge ((offlawGrid 6198 : ℚ) : ℝ) y with hy1 | hy1
      · rw [jointContrib_of_lt g Y r hq1 hy1]
        simp
      rw [jointContrib_of_nonneg_of_le g Y r hdvd hq1 hy0 hy1]
      set k' : Fin 6199 := ⟨offlawIndex y, Nat.lt_succ_of_le (offlawIndex_le _)⟩ with hk'_def
      have hih := ih hq0 (by omega) (D := D - 1) (by omega) k' (childResidue a r)
      have hmono : jointLaw (D - 1) q (childResidue a r) ((offlawGrid k' : ℚ) : ℝ) ≤
          jointLaw (D - 1) q (childResidue a r) y :=
        jointLaw_mono _ _ _ (offlawGrid_offlawIndex_le hy0)
      set Z : ℕ := Y q (childResidue a r) k' with hZ_def
      have hfl : ((⌊((2 : ℝ) ^ a)⁻¹ * (Z : ℝ)⌋₊ : ℕ) : ℝ≥0∞) / 2 ^ 62 ≤
          2⁻¹ ^ a * ((Z : ℝ≥0∞) / 2 ^ 62) := by
        have hZ : ENNReal.ofReal ((Z : ℝ) / 2 ^ 62) ≤ (Z : ℝ≥0∞) / 2 ^ 62 := by
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        refine jointBelow_natCast_div_le ?_ hZ
        refine (Nat.floor_le (by positivity)).trans (le_of_eq ?_)
        field_simp
      exact hfl.trans (by gcongr; exact hih.trans hmono)
    have hrec := jointLaw_eq_tsum (by omega : 1 ≤ q + 1) (by omega : 1 ≤ D) r x
    calc (Y (q + 1) r k : ℝ≥0∞) / 2 ^ 62
        ≤ ((∑ a ∈ Icc 1 60, jointContrib g Y (q + 1) r k a : ℕ) : ℝ≥0∞) / 2 ^ 62 := by
          gcongr
          exact hY (q + 1) hq hq8 k r
      _ = ∑ a ∈ Icc 1 60, (jointContrib g Y (q + 1) r k a : ℝ≥0∞) / 2 ^ 62 := by
          rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
          simp only [div_eq_mul_inv]
      _ ≤ ∑ a ∈ Icc 1 60, T a := Finset.sum_le_sum fun a _ => hdag a
      _ ≤ ∑' a : ℕ+, T a := jointBelow_sum_Icc_le_tsum T
      _ = jointLaw D (q + 1) r x := hrec.symm

end CollatzPosDens
