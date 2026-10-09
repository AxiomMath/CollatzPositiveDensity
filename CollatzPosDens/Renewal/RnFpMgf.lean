/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpFinite
public import CollatzPosDens.Renewal.RnFpFirstStep
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Renewal.RnMgfSummable
public import CollatzPosDens.Renewal.RnHoldJmarginal
public import CollatzPosDens.Renewal.RnHoldMass

/-!
# Exponential moments of the first-passage law

For a level `s ∈ ℕ` and real `t ≥ 0`, the sum in `[0, ∞]` of the series of nonnegative terms
`∑_{(r, ℓ) ∈ ℤ²} F_s(r, ℓ) e^{t r}` is at most `M₄₅(t)^{s+1}`.

Writing `Φ_s` for this sum and `M = M₄₅(t)`, summing the horizontal marginal of the holding-time
law gives `∑_{h ∈ 𝒫} η(h) e^{t j(h)} = ∑_j ν₄₅(j) e^{t j} = M`, and since `t ≥ 0` and `η` has
total mass `1`, `M ≥ 1`. The first-step decomposition of `F_s` gives
`Φ_s = ∑_{l(h) > s} η(h) e^{t j(h)} + ∑_{1 ≤ l(h) ≤ s} η(h) e^{t j(h)} Φ_{s - l(h)}`, and by strong
induction on `s` the right-hand side is at most `(∑_{h ∈ 𝒫} η(h) e^{t j(h)}) M^s = M^{s+1}`.

## Main results

* `CollatzPosDens.tsum_ofReal_firstPassageLaw_mul_exp_le`:
  `∑_{x ∈ ℤ²} F_s(x) e^{t x₁} ≤ M₄₅(t)^{s+1}` in `[0, ∞]`.
* `CollatzPosDens.tsum_ofReal_firstPassageLaw_mul_exp_le_tsum_bkPoints`: the exponential
  moment of `η` over `𝒫` equals `M₄₅(t)`.
* `CollatzPosDens.tsum_ofReal_firstPassageLaw_mul_exp_le_one_le_mgfNu45`: `1 ≤ M₄₅(t)` for
  `t ≥ 0`.

## Implementation notes

The series is summed in `ℝ≥0∞` with terms `ENNReal.ofReal (F_s(x) e^{t x₁})`, so that the sum
lies in `[0, ∞]`; the terms are nonnegative reals. Since the identity
`∑_{h ∈ 𝒫} η(h) e^{t j(h)} = M₄₅(t)` holds in `[0, ∞]` without any convergence hypothesis, the
assumption `11 e^t < 16` (which makes `M₄₅(t)` finite) is not needed: when `M₄₅(t) = ∞` the bound
is trivial. The theorem is therefore stated for all `t ≥ 0`.

## References

* [Mazur, *Collatz positive density*], §6.3.
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- The exponential moment of the holding-time law over the black points is `M₄₅(t)`:
`∑_{p ∈ 𝒫} η(p) e^{t j(p)} = M₄₅(t)` in `[0, ∞]`. -/
theorem tsum_ofReal_firstPassageLaw_mul_exp_le_tsum_bkPoints (t : ℝ) :
    ∑' p : bkPoints, ENNReal.ofReal (holdLaw p.1.1.toNat p.1.2 * exp (t * (p : ℤ × ℤ).1)) =
      mgfNu45 t := by
  rw [← bkPointsEquiv.tsum_eq, ENNReal.tsum_prod', mgfNu45_def]
  refine tsum_congr fun m ↦ ?_
  have hs := (hasSum_holdLaw (j := m + 1) (by omega)).mul_right (exp (t * ((m : ℝ) + 1)))
  have e : ∀ l : ℤ, ENNReal.ofReal (holdLaw ((bkPointsEquiv (m, l)) : ℤ × ℤ).1.toNat
      ((bkPointsEquiv (m, l)) : ℤ × ℤ).2 * exp (t * (((bkPointsEquiv (m, l)) : ℤ × ℤ).1 : ℝ))) =
      ENNReal.ofReal (holdLaw (m + 1) l * exp (t * ((m : ℝ) + 1))) := by
    intro l
    simp [bkPointsEquiv]
  simp only [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun l ↦ mul_nonneg (holdLaw_nonneg _ _) (exp_pos _).le) hs.summable, hs.tsum_eq]
  push_cast
  rfl

/-- `1 ≤ M₄₅(t)` for `t ≥ 0`. -/
theorem tsum_ofReal_firstPassageLaw_mul_exp_le_one_le_mgfNu45 {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ mgfNu45 t := by
  rw [← tsum_ofReal_firstPassageLaw_mul_exp_le_tsum_bkPoints, ← ENNReal.ofReal_one,
    ← tsum_holdLaw_bkPoints, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ holdLaw_nonneg _ _)
      hasSum_holdLaw_bkPoints.summable]
  refine ENNReal.tsum_le_tsum fun p ↦ ENNReal.ofReal_le_ofReal ?_
  have hp : (1 : ℝ) ≤ ((p : ℤ × ℤ).1 : ℝ) := by exact_mod_cast p.2
  exact le_mul_of_one_le_right (holdLaw_nonneg _ _) (one_le_exp (by positivity))

/-- The first-step bound on a single term of the exponential moment of `F_s`. -/
private lemma ofReal_le_first_step (s : ℕ) (t : ℝ) (x : ℤ × ℤ) :
    ENNReal.ofReal (firstPassageLaw s x * exp (t * x.1)) ≤
      (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h},
        ENNReal.ofReal (if x = h.1 then holdLaw h.1.1.toNat h.1.2 * exp (t * (h : ℤ × ℤ).1)
          else 0)) +
      ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
        ENNReal.ofReal ((holdLaw h.1.1.toNat h.1.2 * exp (t * (h : ℤ × ℤ).1)) *
          (firstPassageLaw (s - bkL h) (x - h) * exp (t * (x - h).1))) := by
  classical
  have e₁ : ∀ h : ℤ × ℤ, (holdLaw h.1.toNat h.2 * if x = h then 1 else 0) * exp (t * x.1) =
      if x = h then holdLaw h.1.toNat h.2 * exp (t * h.1) else 0 := by
    intro h
    split_ifs with hx <;> simp [hx]
  have e₂ : ∀ (k : ℤ) (h : ℤ × ℤ),
      holdLaw h.1.toNat h.2 * firstPassageLaw k (x - h) * exp (t * x.1) =
      (holdLaw h.1.toNat h.2 * exp (t * h.1)) *
        (firstPassageLaw k (x - h) * exp (t * (x - h).1)) := by
    intro k h
    rw [show exp (t * x.1) = exp (t * h.1) * exp (t * (x - h).1) by
      rw [← exp_add, Prod.fst_sub, Int.cast_sub]
      ring_nf]
    ring
  rw [firstPassageLaw_eq_first_step, add_mul, ← tsum_mul_right, ← tsum_mul_right]
  simp only [e₁, e₂]
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
  · exact ofReal_tsum_le_tsum_ofReal fun h ↦ by
      split_ifs
      · exact mul_nonneg (holdLaw_nonneg _ _) (exp_pos _).le
      · exact le_rfl
  · exact ofReal_tsum_le_tsum_ofReal fun h ↦
      mul_nonneg (mul_nonneg (holdLaw_nonneg _ _) (exp_pos _).le)
        (mul_nonneg (firstPassageLaw_nonneg _ _) (exp_pos _).le)

/-- Fubini and translation for the second first-step sum. -/
private lemma tsum_second_sum (s : ℕ) (t : ℝ) :
    ∑' x : ℤ × ℤ, ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
      ENNReal.ofReal ((holdLaw h.1.1.toNat h.1.2 * exp (t * (h : ℤ × ℤ).1)) *
        (firstPassageLaw (s - bkL h) (x - h) * exp (t * (x - h).1))) =
    ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
      ENNReal.ofReal (holdLaw h.1.1.toNat h.1.2 * exp (t * (h : ℤ × ℤ).1)) *
        ∑' y : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw (s - bkL h) y * exp (t * y.1)) := by
  rw [ENNReal.tsum_comm]
  congr 1
  ext h
  simp only [ENNReal.ofReal_mul (mul_nonneg (holdLaw_nonneg _ _) (exp_pos _).le),
    ENNReal.tsum_mul_left]
  congr 1
  exact (Equiv.subRight (h : ℤ × ℤ)).tsum_eq
    (fun y ↦ ENNReal.ofReal (firstPassageLaw (s - bkL h) y * exp (t * y.1)))

/-- **Exponential moment of the first-passage law.** For `s ∈ ℕ` and real `t ≥ 0`, the sum in
`[0, ∞]` of the series of nonnegative terms `∑_{(r, ℓ) ∈ ℤ²} F_s(r, ℓ) e^{t r}` is at most
`M₄₅(t)^{s+1}`. -/
@[collatz_pos_dens "lem_rn_fp_mgf"]
theorem tsum_ofReal_firstPassageLaw_mul_exp_le (s : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∑' x : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw s x * exp (t * x.1)) ≤
      mgfNu45 t ^ (s + 1) := by
  classical
  set M := mgfNu45 t
  have hM1 : 1 ≤ M := tsum_ofReal_firstPassageLaw_mul_exp_le_one_le_mgfNu45 ht
  set G : ℤ × ℤ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (holdLaw p.1.toNat p.2 * exp (t * p.1))
    with hG
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  have hA : ∑' x : ℤ × ℤ, ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h},
      ENNReal.ofReal (if x = h.1 then holdLaw h.1.1.toNat h.1.2 * exp (t * (h : ℤ × ℤ).1)
        else 0) =
      ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, G h := by
    rw [ENNReal.tsum_comm]
    congr 1
    ext h
    simp only [apply_ite ENNReal.ofReal, ENNReal.ofReal_zero, tsum_ite_eq, hG]
  have hIH : ∀ h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s},
      ∑' y : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw (s - bkL h) y * exp (t * y.1)) ≤ M ^ s := by
    rintro ⟨h, hP, hl₁, hls⟩
    have hcast : (s : ℤ) - bkL h = ((s - (bkL h).toNat : ℕ) : ℤ) := by omega
    simp only [hcast]
    exact (ih _ (by omega)).trans (pow_le_pow_right₀ hM1 (by omega))
  calc ∑' x : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw s x * exp (t * x.1))
      ≤ (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, G h) +
        ∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}, G h *
          ∑' y : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw (s - bkL h) y * exp (t * y.1)) := by
        refine (ENNReal.tsum_le_tsum (ofReal_le_first_step s t)).trans_eq ?_
        rw [ENNReal.tsum_add, hA, tsum_second_sum]
    _ ≤ (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ (s : ℤ) < bkL h}, G h) * M ^ s +
        (∑' h : {h : ℤ × ℤ // h ∈ bkPoints ∧ 1 ≤ bkL h ∧ bkL h ≤ s}, G h) * M ^ s := by
        refine add_le_add (le_mul_of_one_le_right' (one_le_pow₀ hM1)) ?_
        rw [← ENNReal.tsum_mul_right]
        exact ENNReal.tsum_le_tsum fun h ↦ mul_le_mul_of_nonneg_left (hIH h) bot_le
    _ ≤ M * M ^ s := by
        rw [← add_mul]
        gcongr
        exact (tsum_split_le_tsum_bkPoints s G).trans_eq
          (tsum_ofReal_firstPassageLaw_mul_exp_le_tsum_bkPoints t)
    _ = M ^ (s + 1) := (pow_succ' M s).symm

end CollatzPosDens
