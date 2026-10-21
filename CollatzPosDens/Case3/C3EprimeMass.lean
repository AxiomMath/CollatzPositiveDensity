/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3HorSmall
public import CollatzPosDens.Case3.C3InitEvent
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnHorTailSharp
public import CollatzPosDens.Renewal.RnOvershootTail
public import CollatzPosDens.Transfer.S02UoLem
public import Mathlib.Algebra.Order.Group.Indicator

/-!
# Mass of the initial deviation set

Let `ι ∈ 𝔍` be a Fourier index and `g ≥ 2^32` an integer. The initial deviation set `𝓘_g(ι)`
(`c3InitEvent ι g`) has first-passage mass `∑_{x ∈ 𝓘_g(ι)} F_g(x) ≤ U_o(ι) + (2g)^{-1/2}`.

The set `𝓘_g(ι)` is the union of two events, and the union bound reduces the claim to two tails
of the first-passage law `F_g`:
* the overshoot `ℓ - g ≥ X_o(ι)`, where `X_o(ι) ∈ {194, 182}`: as `g ≥ 64` and `X_o(ι) ≥ 1`, the
  overshoot tail of `F_g` has mass at most `9 (25/27)^{X_o(ι)} ≤ U_o(ι)`;
* the horizontal deviation `|r - g/4| ≥ g/32`: as `g ≥ 6` and `u = g/32 ≥ 2`, the sharp
  horizontal tail of `F_g` at `u` has mass at most `4 exp(-u²/(2(g - 4))) + 2 exp(-u/256)`. As
  `0 < 2(g - 4) < 2g`, the first exponent is at most `-g/2048 ≤ -g/8192`, and `u/256 = g/8192`,
  so this is at most `6 exp(-g/8192) < (2g)^{-1/2}`.

## Main results

* `CollatzPosDens.tsum_firstPassageLaw_c3InitEvent_le`:
  `∑_{x ∈ 𝓘_g(ι)} F_g(x) ≤ U_o(ι) + (2g)^{-1/2}` for `g ≥ 2^32`.
* `CollatzPosDens.tsum_ofReal_firstPassageLaw_c3InitEvent_le`: the same bound, as a sum in
  `[0, ∞]`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal
open Real

/-- The overshoot part: `ℓ - g ≥ X` has `F_g`-mass at most `9 (25/27)^X`, for `g ≥ 64`,
`X ≥ 1`. -/
private lemma c3EprimeMass_overshoot {g X : ℕ} (hg : 64 ≤ g) (hX : 1 ≤ X) :
    ∑' x : ℤ × ℤ, {x : ℤ × ℤ | (X : ℤ) ≤ x.2 - g}.indicator
        (fun x ↦ ENNReal.ofReal (firstPassageLaw g x)) x ≤
      ENNReal.ofReal (9 * (25 / 27) ^ X) := by
  refine (ENNReal.tsum_prod (f := fun r ℓ ↦ {x : ℤ × ℤ | (X : ℤ) ≤ x.2 - g}.indicator
    (fun x ↦ ENNReal.ofReal (firstPassageLaw g x)) (r, ℓ))).trans_le ?_
  refine le_trans (le_of_eq (tsum_congr fun r ↦ ?_))
    (tsum_firstPassageLaw_overshoot_lt g X hg hX).le
  refine Eq.trans ?_ (tsum_subtype {ℓ : ℤ | (g : ℤ) + X ≤ ℓ}
    fun ℓ ↦ ENNReal.ofReal (firstPassageLaw g (r, ℓ))).symm
  refine tsum_congr fun ℓ ↦ ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  congr 1
  exact propext (by omega)

/-- The horizontal part: for `g ≥ 6` and `u ≥ 2`, `|r - g/4| ≥ u` has `F_g`-mass at most
`4 exp(-u²/(2(g - 4))) + 2 exp(-u/256)`. -/
private lemma c3EprimeMass_hor {g : ℕ} (hg : 6 ≤ g) {u : ℝ} (hu : 2 ≤ u) :
    ∑' x : ℤ × ℤ, {x : ℤ × ℤ | u ≤ |(x.1 : ℝ) - g / 4|}.indicator
        (fun x ↦ ENNReal.ofReal (firstPassageLaw g x)) x ≤
      ENNReal.ofReal (4 * exp (-(u ^ 2 / (2 * ((g : ℝ) - 4)))) + 2 * exp (-(u / 256))) := by
  set S : Set ℤ := {r : ℤ | u ≤ |(r : ℝ) - g / 4|}
  set f : ℤ → ℝ≥0∞ := fun r ↦ ∑' ℓ : ℤ, ENNReal.ofReal (firstPassageLaw g (r, ℓ)) with hf
  have hF := summable_firstPassageLaw g
  refine (ENNReal.tsum_prod (f := fun r ℓ ↦ {x : ℤ × ℤ | u ≤ |(x.1 : ℝ) - g / 4|}.indicator
    (fun x ↦ ENNReal.ofReal (firstPassageLaw g x)) (r, ℓ))).trans_le ?_
  calc _ = ∑' r : ℤ, S.indicator f r := by
        refine tsum_congr fun r ↦ ?_
        by_cases hr : r ∈ S
        · rw [Set.indicator_of_mem hr, hf]
          exact tsum_congr fun ℓ ↦ Set.indicator_of_mem (show ((r, ℓ) : ℤ × ℤ) ∈
            {x : ℤ × ℤ | u ≤ |(x.1 : ℝ) - g / 4|} from hr) _
        · rw [Set.indicator_of_notMem hr]
          exact ENNReal.tsum_eq_zero.2 fun ℓ ↦ Set.indicator_of_notMem (show ((r, ℓ) : ℤ × ℤ) ∉
            {x : ℤ × ℤ | u ≤ |(x.1 : ℝ) - g / 4|} from hr) _
    _ = ∑' r : S, f r := (tsum_subtype S f).symm
    _ = ∑' r : S, ENNReal.ofReal (∑' ℓ : ℤ, firstPassageLaw g (r, ℓ)) := by
        refine tsum_congr fun r ↦ ?_
        rw [hf, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ firstPassageLaw_nonneg _ _)
          (hF.prod_factor r.1)]
    _ = ENNReal.ofReal (∑' r : S, ∑' ℓ : ℤ, firstPassageLaw g (r, ℓ)) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun _ ↦ tsum_nonneg fun _ ↦ firstPassageLaw_nonneg _ _)
          (summable_firstPassageLaw_hor_tail g u)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (tsum_firstPassageLaw_hor_tail_le_of_six_le hg hu)

/-- At `u = g/32` the sharp horizontal tail bound is at most `6 exp(-g/8192)`, for `g > 4`. -/
private lemma c3EprimeMass_horTail_le {g : ℝ} (hg : 4 < g) :
    4 * exp (-((g / 32) ^ 2 / (2 * (g - 4)))) + 2 * exp (-(g / 32 / 256)) ≤
      6 * exp (-g / 8192) := by
  have h1 : exp (-((g / 32) ^ 2 / (2 * (g - 4)))) ≤ exp (-g / 8192) := by
    rw [exp_le_exp, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by linarith)]
    nlinarith
  have h2 : exp (-(g / 32 / 256)) = exp (-g / 8192) := by
    congr 1; ring
  linarith

/-- **Mass of the initial deviation set**, as a sum in `[0, ∞]`: for `ι ∈ 𝔍` and `g ≥ 2^32`,
`∑_{x ∈ 𝓘_g(ι)} F_g(x) ≤ U_o(ι) + (2g)^{-1/2}`. -/
theorem tsum_ofReal_firstPassageLaw_c3InitEvent_le (ι : FIndex) {g : ℕ} (hg : 2 ^ 32 ≤ g) :
    ∑' x : c3InitEvent ι g, ENNReal.ofReal (firstPassageLaw g x) ≤
      ENNReal.ofReal (Uo ι + (2 * g) ^ (-1 / 2 : ℝ)) := by
  set F : ℤ × ℤ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (firstPassageLaw g x)
  set A : Set (ℤ × ℤ) := {x | (overshootAllowance ι : ℤ) ≤ x.2 - g}
  set B : Set (ℤ × ℤ) := {x | (g : ℝ) / 32 ≤ |(x.1 : ℝ) - g / 4|}
  have hg64 : 64 ≤ g := le_trans (by norm_num) hg
  have hgR : (2 : ℝ) ^ 32 ≤ g := by exact_mod_cast hg
  have hunion : ∀ x, (c3InitEvent ι g).indicator F x ≤ A.indicator F x + B.indicator F x := by
    intro x
    by_cases hA : x ∈ A
    · rw [Set.indicator_of_mem hA]
      exact le_add_right (Set.indicator_le_self _ _ x)
    · by_cases hB : x ∈ B
      · rw [Set.indicator_of_mem hB]
        exact le_add_left (Set.indicator_le_self _ _ x)
      · have : x ∉ c3InitEvent ι g := fun h ↦ h.elim hA hB
        rw [Set.indicator_of_notMem this]
        exact bot_le
  calc ∑' x : c3InitEvent ι g, F x = ∑' x, (c3InitEvent ι g).indicator F x := tsum_subtype _ F
    _ ≤ ∑' x, (A.indicator F x + B.indicator F x) := ENNReal.tsum_le_tsum hunion
    _ = ∑' x, A.indicator F x + ∑' x, B.indicator F x := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (9 * (25 / 27) ^ overshootAllowance ι) +
          ENNReal.ofReal (4 * exp (-(((g : ℝ) / 32) ^ 2 / (2 * ((g : ℝ) - 4)))) +
            2 * exp (-((g : ℝ) / 32 / 256))) :=
        add_le_add (c3EprimeMass_overshoot hg64 (overshootAllowance_pos ι))
          (c3EprimeMass_hor (by omega) (by rw [le_div_iff₀ (by norm_num)]; linarith))
    _ ≤ ENNReal.ofReal (Uo ι) + ENNReal.ofReal ((2 * g) ^ (-1 / 2 : ℝ)) := by
        gcongr
        · exact nine_mul_pow_overshootAllowance_le_Uo_cast ι
        · exact ((c3EprimeMass_horTail_le (lt_of_lt_of_le (by norm_num) hgR)).trans_lt
            (c3HorSmall hgR)).le
    _ = _ := (ENNReal.ofReal_add (by exact_mod_cast (Uo_pos ι).le) (by positivity)).symm

/-- **Mass of the initial deviation set.** For `ι ∈ 𝔍` and `g ≥ 2^32`,
`∑_{x ∈ 𝓘_g(ι)} F_g(x) ≤ U_o(ι) + (2g)^{-1/2}`. -/
@[collatz_pos_dens "lem_c3_eprime_mass"]
theorem tsum_firstPassageLaw_c3InitEvent_le (ι : FIndex) {g : ℕ} (hg : 2 ^ 32 ≤ g) :
    ∑' x : c3InitEvent ι g, firstPassageLaw g x ≤ Uo ι + (2 * g) ^ (-1 / 2 : ℝ) := by
  have h := tsum_ofReal_firstPassageLaw_c3InitEvent_le ι hg
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ firstPassageLaw_nonneg _ _)
    ((summable_firstPassageLaw g).subtype _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (by exact_mod_cast (Uo_pos ι).le) (by positivity))).1 h

end CollatzPosDens
