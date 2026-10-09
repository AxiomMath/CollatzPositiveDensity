/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Monotone.MoRate
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Monotone.MoEnvelope
public import CollatzPosDens.Monotone.MoInvpowSummable
public import CollatzPosDens.Monotone.MoRateD1
public import CollatzPosDens.Renewal.RnMgfBound

/-!
# The `ν₄₅`-average of the inverse power

Let `A ≥ 0` and `0 < w ≤ 1/32` be reals and let `m` be an integer with `m ≥ (256A/w)^2 + 2`.
Then `∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A} ≤ m^{-A} e^{w/2}`.

Put `t = moRate A m`; then `0 ≤ t ≤ w/32 ≤ 1/1024`. By
`max_sub_one_rpow_neg_le_mul_exp_moRate` each term is at most `m^{-A} ν₄₅(r) e^{t r}`, and the
series `∑_{r ≥ 1} ν₄₅(r) e^{t r}` is the exponential moment `M₄₅(t) ≤ e^{13t/4}`
(`mgfNu45_le_exp`). Comparing termwise, the left side is at most
`m^{-A} e^{13t/4} ≤ m^{-A} e^{13w/128} ≤ m^{-A} e^{w/2}`.

## Main results

* `CollatzPosDens.tsum_nu45_mul_max_rpow_neg_le`: the bound above.

## Implementation notes

The summation index `r ≥ 1` is written as `r + 1` with `r : ℕ`, and the power
`max(m - r, 1)^{-A}` is the real power `Real.rpow` of the integer `max(m - r, 1)` cast to `ℝ`,
as in `summable_nu45_mul_max_rpow_neg`. Since `m ≥ 2`, the integer `m` is identified with the
natural number `m.toNat` when `max_sub_one_rpow_neg_le_mul_exp_moRate` and `moRate` (defined on
`ℕ`) are used. The finiteness of `M₄₅(t)`, which gives convergence of the real majorant series,
is read off from the bound `M₄₅(t) ≤ e^{13t/4}`.

## References

* [Mazur, *Collatz positive density*], §8.2.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **The `ν₄₅`-average of the inverse power.** For reals `A ≥ 0`, `0 < w ≤ 1/32` and an
integer `m ≥ (256A/w)^2 + 2`, `∑_{r ≥ 1} ν₄₅(r) max(m - r, 1)^{-A} ≤ m^{-A} e^{w/2}`. -/
@[collatz_pos_dens "lem_mo_invpow_moment"]
theorem tsum_nu45_mul_max_rpow_neg_le {A w : ℝ} (hA : 0 ≤ A) (hw₀ : 0 < w) (hw₁ : w ≤ 1 / 32)
    {m : ℤ} (hm : (256 * A / w) ^ 2 + 2 ≤ (m : ℝ)) :
    ∑' r : ℕ, nu45 ((r : ℤ) + 1) * (((max (m - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A)) ≤
      (m : ℝ) ^ (-A) * exp (w / 2) := by
  have hm2 : (2 : ℝ) ≤ m := by nlinarith [sq_nonneg (256 * A / w)]
  have hm2' : (2 : ℤ) ≤ m := by exact_mod_cast hm2
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, by omega⟩
  have hn : 1 ≤ n := by omega
  have hmn : (256 * A / w) ^ 2 + 2 ≤ (n : ℝ) := by exact_mod_cast hm
  set t := moRate A n
  have ht₀ : 0 ≤ t := moRate_nonneg hA n
  have htw : t ≤ w / 32 := moRate_le_div_thirtyTwo hA hw₀ hmn
  have ht₁ : t ≤ 1 / 1024 := by linarith
  set g : ℕ → ℝ := fun r ↦ nu45 ((r : ℤ) + 1) * exp (t * ((r : ℝ) + 1)) with hg
  have hg0 : ∀ r, 0 ≤ g r := fun r ↦ mul_nonneg (nu45_nonneg _) (exp_pos _).le
  have hM := mgfNu45_le_exp ht₀ ht₁
  rw [mgfNu45_def] at hM
  have hne : ∑' r : ℕ, ENNReal.ofReal (g r) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM
  have hgs : Summable g := by
    simpa [ENNReal.toReal_ofReal (hg0 _)] using ENNReal.summable_toReal hne
  have hgsum : ∑' r, g r ≤ exp (13 * t / 4) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hgs] at hM
    exact (ENNReal.ofReal_le_ofReal_iff (exp_pos _).le).mp hM
  have hbound : ∀ r : ℕ,
      nu45 ((r : ℤ) + 1) * ((((max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ)) : ℝ) ^ (-A)) ≤
        (n : ℝ) ^ (-A) * g r := by
    intro r
    have hcast : (((max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ)) : ℝ) =
        ((max (n - (r + 1)) 1 : ℕ) : ℝ) := by
      rw [show (max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ) = ((max (n - (r + 1)) 1 : ℕ) : ℤ) by omega,
        Int.cast_natCast]
    rw [hcast]
    calc nu45 ((r : ℤ) + 1) * ((max (n - (r + 1)) 1 : ℕ) : ℝ) ^ (-A)
        ≤ nu45 ((r : ℤ) + 1) * ((n : ℝ) ^ (-A) * exp (t * ((r : ℝ) + 1))) := by
          gcongr
          · exact nu45_nonneg _
          · simpa using max_sub_one_rpow_neg_le_mul_exp_moRate hA hn (r + 1)
      _ = (n : ℝ) ^ (-A) * g r := by
          rw [hg]
          ring
  calc ∑' r : ℕ, nu45 ((r : ℤ) + 1) * ((((max ((n : ℤ) - ((r : ℤ) + 1)) 1 : ℤ)) : ℝ) ^ (-A))
      ≤ ∑' r, (n : ℝ) ^ (-A) * g r :=
        (summable_nu45_mul_max_rpow_neg A (n : ℤ)).tsum_le_tsum hbound (hgs.mul_left _)
    _ = (n : ℝ) ^ (-A) * ∑' r, g r := tsum_mul_left
    _ ≤ (n : ℝ) ^ (-A) * exp (13 * t / 4) := by gcongr
    _ ≤ ((n : ℤ) : ℝ) ^ (-A) * exp (w / 2) := by
          rw [Int.cast_natCast]
          exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end CollatzPosDens
