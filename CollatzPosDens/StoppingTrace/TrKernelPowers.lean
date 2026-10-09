/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Rho
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrDeltaNonneg
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrKernelOne
public import CollatzPosDens.StoppingTrace.TrKernelTwo
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# Powers of the entry kernel at black points

Fix a level `n` and a unit `ξ ∈ G_n`. A black point is a point `v ∈ 𝒫` (`bkPoints`) satisfying
`BkBlack n ξ ε_* v`, where `ε_* = epsStar`. Write `m_k = trKernel n ξ k` for the `k`-th power of
the entry kernel, `d_* = dStar` and `ϱ_* = rhoStar`. For every black point `v` and every
`k ∈ ℕ`,
```
m_k(v) ≤ ϱ_*^{⌊k/2⌋} (1 - d_*)^{k - 2⌊k/2⌋}.
```
Write `c_k` for the right side, so that `c_{k+2} = ϱ_* c_k`. The bound holds for `k = 0` since
`m_0 = 1`, and for `k = 1` by the one-step bound `m_1(v) ≤ 1 - d_* - δ_tr(gap(v))` and
`δ_tr ≥ 0`. For the step from `k` to `k + 2`, a bound `m_k ≤ c` at every black point propagates
along the kernel: `m_{j+k}(v) ≤ c · m_j(v)` at every black point, by induction on `j`, since the
endpoints `x_{|u|}(v, u)` of entry lists are black points. With `j = 2` and the two-step rate
`m_2 ≤ ϱ_*` this gives `m_{k+2}(v) ≤ ϱ_* c_k = c_{k+2}`.

## Main results

* `CollatzPosDens.trKernel_le_rhoStar_pow`: `m_k(v) ≤ ϱ_*^{⌊k/2⌋} (1 - d_*)^{k - 2⌊k/2⌋}`
  for every black point `v`.
* `CollatzPosDens.trKernel_le_rhoStar_pow_add_le_mul`: if `m_k ≤ c` at every black point,
  then `m_{j+k}(v) ≤ c · m_j(v)` at every black point.

## Implementation notes

The value `m_k(v)` lies in `[0, ∞]`, and the bound is stated there against
`ENNReal.ofReal c_k`; since `c_k > 0` this is equivalent to the real inequality. No hypothesis
`n ≥ 1` is needed.

## References

* [Mazur, *Collatz positive density*], §9.6.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n}

/-- **Propagation along the kernel.** If `m_k ≤ c` at every black point, then
`m_{j+k}(v) ≤ c · m_j(v)` at every black point `v`. -/
theorem trKernel_le_rhoStar_pow_add_le_mul {k : ℕ} {c : ℝ≥0∞}
    (hc : ∀ w ∈ bkPoints, BkBlack n ξ (epsStar : ℝ) w → trKernel n ξ k w ≤ c) :
    ∀ (j : ℕ) {v : ℤ × ℤ}, v ∈ bkPoints → BkBlack n ξ (epsStar : ℝ) v →
      trKernel n ξ (j + k) v ≤ c * trKernel n ξ j v := by
  intro j
  induction j with
  | zero => intro v hv hb; simpa using hc v hv hb
  | succ j ih =>
    intro v hv _
    rw [show j + 1 + k = (j + k) + 1 by omega, trKernel_succ, trKernel_succ,
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun u ↦ ?_
    have h := ih (trPath_mem_bkPoints hv u.1 u.1.length) (trEntryWords_bkBlack u.2)
    calc _ ≤ ENNReal.ofReal (trListWeight u.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v u.1 u.1.length)) *
            (c * trKernel n ξ j (trPath v u.1 u.1.length)) := by gcongr
      _ = _ := by ring

/-- **Powers of the kernel.** Let `ξ ∈ G_n` be a unit. For every black point `v ∈ 𝒫` and every
`k ∈ ℕ`, `m_k(v) ≤ ϱ_*^{⌊k/2⌋} (1 - d_*)^{k - 2⌊k/2⌋}`. -/
@[collatz_pos_dens "lem_tr_kernel_powers"]
theorem trKernel_le_rhoStar_pow (hξ : IsResidueUnit ξ) (k : ℕ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) :
    trKernel n ξ k v ≤
      ENNReal.ofReal ((rhoStar : ℝ) ^ (k / 2) * (1 - (dStar : ℝ)) ^ (k - 2 * (k / 2))) := by
  set C : ℕ → ℝ := fun k ↦ (rhoStar : ℝ) ^ (k / 2) * (1 - (dStar : ℝ)) ^ (k - 2 * (k / 2))
    with hC
  have hρ0 : (0 : ℝ) ≤ rhoStar := by exact_mod_cast rhoStar_pos.le
  have hd : (0 : ℝ) ≤ 1 - (dStar : ℝ) := by
    have : (dStar : ℝ) < 1 := by exact_mod_cast dStar_lt_one
    linarith
  have hC0 : ∀ k, 0 ≤ C k := fun k ↦ mul_nonneg (pow_nonneg hρ0 _) (pow_nonneg hd _)
  have hC2 : ∀ k, C (k + 2) = C k * rhoStar := by
    intro k
    simp only [hC]
    rw [show (k + 2) / 2 = k / 2 + 1 by omega, show k + 2 - 2 * (k / 2 + 1) = k - 2 * (k / 2) by
      omega, pow_succ]
    ring
  suffices H : ∀ k, (∀ w ∈ bkPoints, BkBlack n ξ (epsStar : ℝ) w →
      trKernel n ξ k w ≤ ENNReal.ofReal (C k)) ∧ (∀ w ∈ bkPoints, BkBlack n ξ (epsStar : ℝ) w →
      trKernel n ξ (k + 1) w ≤ ENNReal.ofReal (C (k + 1))) from (H k).1 v hv hb
  have hstep : ∀ k, (∀ w ∈ bkPoints, BkBlack n ξ (epsStar : ℝ) w →
      trKernel n ξ k w ≤ ENNReal.ofReal (C k)) → ∀ w ∈ bkPoints, BkBlack n ξ (epsStar : ℝ) w →
      trKernel n ξ (k + 2) w ≤ ENNReal.ofReal (C (k + 2)) := by
    intro k hk w hw hbw
    calc trKernel n ξ (k + 2) w = trKernel n ξ (2 + k) w := by rw [add_comm]
      _ ≤ ENNReal.ofReal (C k) * trKernel n ξ 2 w :=
        trKernel_le_rhoStar_pow_add_le_mul hk 2 hw hbw
      _ ≤ ENNReal.ofReal (C k) * ENNReal.ofReal (rhoStar : ℝ) := by
        gcongr; exact trKernel_two_le_rhoStar hξ hw hbw
      _ = ENNReal.ofReal (C (k + 2)) := by rw [hC2, ENNReal.ofReal_mul (hC0 k)]
  intro k
  induction k with
  | zero =>
    refine ⟨fun w _ _ ↦ by simp [hC], fun w hw hbw ↦ ?_⟩
    refine (trKernel_one_le hξ hw hbw).trans (ENNReal.ofReal_le_ofReal ?_)
    have := trDelta_nonneg (trGap n ξ (epsStar : ℝ) w)
    have h1 : C 1 = 1 - (dStar : ℝ) := by simp [hC]
    rw [zero_add, h1]
    linarith
  | succ k ih => exact ⟨ih.2, hstep k ih.1⟩

end CollatzPosDens
