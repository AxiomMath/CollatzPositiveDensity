/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChDist
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldJmarginal
public import CollatzPosDens.FourierDecay.ChGap
public import CollatzPosDens.FourierDecay.ChRealMoment

/-!
# The expectation of the renewal function under the holding-time law

Let `0 < A ≤ 5` be real and suppose the renewal function decays polynomially in the distance to
the cut-off: `Q(p) ≤ D^A d_J(p)^{-A}` for every `p ∈ 𝒫`. Then its expectation under the
holding-time law `η` is small: `∑_{h ∈ 𝒫} η(h) Q(h) ≤ (160 D)^A / n^A`.

Indeed the gap inequality `n ≤ 8 j(h) d_J(h)` gives `Q(h) ≤ D^A 8^A n^{-A} j(h)^A`. Grouping the
sum by the first coordinate, the horizontal marginal of `η` turns `∑_h η(h) j(h)^A` into the
real moment `∑_{j ≥ 1} ν₄₅(j) j^A ≤ 20^A`, and `8 · 20 = 160`.

## Main results

* `CollatzPosDens.holdLaw_chQ_expectation_le`: the series `∑_{h ∈ 𝒫} η(h) Q(h)` converges and
  its sum is at most `(160 D)^A / n^A`.

## Implementation notes

The law `η` is `holdLaw`, indexed by `(j, l) ∈ ℕ × ℤ`; at `h ∈ 𝒫` it is evaluated at
`(j(h), l(h))`, the first coordinate converted to `ℕ` (it is positive on `𝒫`). The sum over `𝒫`
is a `tsum` over the subtype `bkPoints`, and its convergence is part of the conclusion. The
power `d_J(p)^{-A}` is the real power `Real.rpow`. The hypotheses `A ≥ 1` and `D ≥ 1` of the
paper are weakened to `A > 0` and `D ∈ ℕ`; the level `n` is assumed positive.

## References

* [Mazur, *Collatz positive density*], §12.
-/

@[expose] public section

namespace CollatzPosDens

/-- Grouping by the first coordinate: `∑_{h ∈ 𝒫} η(h) j(h)^A` converges and is at most
`∑_{j ≥ 1} ν₄₅(j) j^A ≤ 20^A`. -/
private lemma holdLaw_mul_rpow_le {A : ℝ} (hA : 0 < A) (hA5 : A ≤ 5) :
    Summable (fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * (h.1.1 : ℝ) ^ A) ∧
      ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * (h.1.1 : ℝ) ^ A ≤ 20 ^ A := by
  obtain ⟨hsm, hle⟩ := nu45_rpow_moment_le hA hA5
  set F : bkPoints → ℝ := fun h ↦ holdLaw h.1.1.toNat h.1.2 * (h.1.1 : ℝ) ^ A
  set f : ℕ × ℤ → ℝ := fun x ↦ holdLaw (x.1 + 1) x.2 * (((x.1 : ℤ) + 1 : ℤ) : ℝ) ^ A
  have hf : F ∘ bkPointsEquiv = f := by
    funext x
    simp only [F, f, Function.comp, bkPointsEquiv, Equiv.coe_fn_mk]
    rw [show ((x.1 : ℤ) + 1).toNat = x.1 + 1 by omega]
  have h0 : 0 ≤ f := fun x ↦ mul_nonneg (holdLaw_nonneg _ _) (Real.rpow_nonneg (by positivity) _)
  have hfib : ∀ m : ℕ, HasSum (fun l : ℤ ↦ f (m, l))
      (nu45 ((m : ℤ) + 1) * (((m : ℤ) + 1 : ℤ) : ℝ) ^ A) := fun m ↦ by
    simpa [f] using (hasSum_holdLaw (j := m + 1) (by omega)).mul_right ((((m : ℤ) + 1 : ℤ) : ℝ) ^ A)
  have hinj : Function.Injective fun m : ℕ ↦ (m : ℤ) + 1 := fun a b h ↦ by simpa using h
  have hgnn : ∀ j : ℤ, 0 ≤ nu45 j * (j : ℝ) ^ A := fun j ↦ by
    rcases le_or_gt j 0 with hj | hj
    · simp [nu45_of_nonpos hj]
    · exact mul_nonneg (nu45_nonneg j) (Real.rpow_nonneg (by exact_mod_cast hj.le) _)
  have hs : Summable f := by
    rw [summable_prod_of_nonneg h0]
    refine ⟨fun m ↦ (hfib m).summable, ?_⟩
    simp_rw [(hfib _).tsum_eq]
    exact hsm.comp_injective hinj
  refine ⟨by rwa [← bkPointsEquiv.summable_iff, hf], ?_⟩
  calc ∑' h, F h = ∑' x, f x := by
        rw [← hf]
        exact (bkPointsEquiv.tsum_eq F).symm
    _ = ∑' m : ℕ, nu45 ((m : ℤ) + 1) * (((m : ℤ) + 1 : ℤ) : ℝ) ^ A := by
      rw [hs.tsum_prod]
      exact tsum_congr fun m ↦ (hfib m).tsum_eq
    _ ≤ ∑' j : ℤ, nu45 j * (j : ℝ) ^ A :=
      tsum_comp_le_tsum_of_inj hsm hgnn hinj
    _ ≤ 20 ^ A := hle

/-- **Expectation of the renewal function under the holding-time law.** Let `0 < A ≤ 5` and
suppose `Q(p) ≤ D^A d_J(p)^{-A}` for every `p ∈ 𝒫`. Then `∑_{h ∈ 𝒫} η(h) Q(h)` converges and
`∑_{h ∈ 𝒫} η(h) Q(h) ≤ (160 D)^A / n^A`. -/
@[collatz_pos_dens "lem_ch_hold_expectation"]
theorem holdLaw_chQ_expectation_le {n : ℕ} (hn : 1 ≤ n) (ξ : ResidueGroup n) (ε : ℝ)
    {A : ℝ} (hA : 0 < A) (hA5 : A ≤ 5) (D : ℕ)
    (hQ : ∀ p ∈ bkPoints, chQ n ξ ε p ≤ (D : ℝ) ^ A * (chDist n p : ℝ) ^ (-A)) :
    Summable (fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε h) ∧
      ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε h ≤
        (160 * D : ℝ) ^ A / (n : ℝ) ^ A := by
  obtain ⟨hsg, hleg⟩ := holdLaw_mul_rpow_le hA hA5
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set C : ℝ := (D : ℝ) ^ A * 8 ^ A / (n : ℝ) ^ A
  have hterm : ∀ h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε h ≤
      C * (holdLaw h.1.1.toNat h.1.2 * (h.1.1 : ℝ) ^ A) := by
    rintro ⟨p, hp⟩
    have hj : 1 ≤ p.1 := hp
    have hgap := le_eight_mul_max_half_sub n (j := p.1.toNat) (by omega)
    have hd : max (n / 2 - p.1.toNat) 1 = chDist n p := by
      unfold chDist bkJ
      congr 1
      omega
    rw [hd] at hgap
    have hdpos : (0 : ℝ) < chDist n p := by exact_mod_cast chDist_pos n p
    have hjR : (p.1 : ℝ) = ((p.1.toNat : ℕ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    have hgapR : (n : ℝ) ≤ 8 * ((p.1.toNat : ℕ) : ℝ) * chDist n p := by exact_mod_cast hgap
    have key : (D : ℝ) ^ A * (chDist n p : ℝ) ^ (-A) ≤ C * (p.1 : ℝ) ^ A := by
      rw [Real.rpow_neg hdpos.le, ← div_eq_mul_inv, hjR, div_le_iff₀ (by positivity)]
      have hpow : (n : ℝ) ^ A ≤ (8 * ((p.1.toNat : ℕ) : ℝ) * chDist n p) ^ A :=
        Real.rpow_le_rpow hnR.le hgapR hA.le
      rw [Real.mul_rpow (by positivity) hdpos.le,
        Real.mul_rpow (by norm_num) (by positivity)] at hpow
      simp only [C]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      calc (D : ℝ) ^ A * (n : ℝ) ^ A
          ≤ (D : ℝ) ^ A * ((8 : ℝ) ^ A * ((p.1.toNat : ℕ) : ℝ) ^ A * (chDist n p : ℝ) ^ A) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = _ := by ring
    calc holdLaw p.1.toNat p.2 * chQ n ξ ε p
        ≤ holdLaw p.1.toNat p.2 * (C * (p.1 : ℝ) ^ A) :=
          mul_le_mul_of_nonneg_left ((hQ p hp).trans key) (holdLaw_nonneg _ _)
      _ = C * (holdLaw p.1.toNat p.2 * (p.1 : ℝ) ^ A) := by ring
  have hg := hsg.hasSum.mul_left C
  have hsf : Summable fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε h :=
    hg.summable.of_nonneg_of_le
      (fun h ↦ mul_nonneg (holdLaw_nonneg _ _) (chQ_nonneg _ _ _ _)) hterm
  refine ⟨hsf, ?_⟩
  calc ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε h
      ≤ C * ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * (h.1.1 : ℝ) ^ A :=
        hasSum_le hterm hsf.hasSum hg
    _ ≤ C * 20 ^ A := mul_le_mul_of_nonneg_left hleg (by positivity)
    _ = (160 * D : ℝ) ^ A / (n : ℝ) ^ A := by
        simp only [C]
        rw [show (160 * D : ℝ) = D * 8 * 20 by ring,
          Real.mul_rpow (by positivity) (by norm_num), Real.mul_rpow (by positivity) (by norm_num)]
        ring

end CollatzPosDens
