/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Amix
public import CollatzPosDens.Transfer.S02Bstar
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxOscSubadditive
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxSubmassLe
public import CollatzPosDens.Mixing.MxSubmassUnion
public import CollatzPosDens.Mixing.MxShHeight
public import CollatzPosDens.Mixing.MxShJ
public import CollatzPosDens.Mixing.MxShKhi
public import CollatzPosDens.Mixing.MxShKlo
public import CollatzPosDens.Mixing.MxShGate
public import CollatzPosDens.Mixing.MxShShellWidth
public import CollatzPosDens.Mixing.MxShSlice
public import CollatzPosDens.Mixing.MxShRetained
public import CollatzPosDens.Mixing.MxShGateMass
public import CollatzPosDens.Mixing.MxShGateOsc
public import CollatzPosDens.Mixing.MxShRenyi
public import CollatzPosDens.Mixing.MxShShellSum
public import CollatzPosDens.Mixing.MxShShellCount
public import CollatzPosDens.Mixing.MxShSlicesDisjoint
public import CollatzPosDens.Mixing.MxShWindowLow

/-!
# Oscillation of the retained part of the shell cut

Let `ι` be a Fourier index, and let `n ≥ n₀ = 2^80` and `m ≤ n` with `25 n ≤ 27 m`. Then the
submass of the retained words `R^{sh}_n` of the shell cut satisfies
$$\mathrm{Osc}_{m,n}\bigl(\mathrm{Sub}^n_{\mathcal R^{\mathrm{sh}}_n}\bigr)
  \le 18\, B_{\mathrm F}(ι)\, n^{-a_{\mathrm{mx}}(ι)} \log n.$$

Write `H = H^{sh}_n`, `N = H - 1`, `J = J^{sh}_n` and `Λ = B_F(ι) n^{-A_*(ι)}`. The slices
`Sl^{sh}_n(d, j)` making up `R^{sh}_n` are pairwise disjoint, so the submass is the sum of the
submasses of the slices, and the oscillation is subadditive. Each slice contributes at most
`Λ √((W_j + 2) 2^{-N} #Hd^{sh}_n(d, j))`, and `#Hd^{sh}_n(d, j) ≤ C(N, d) min(1, 2^{4-j})`, so
the root factors into `√(C(N, d) 2^{-N})`, depending on `d` only, and
`√((W_j + 2) min(1, 2^{4-j}))`, depending on `j` only. The sum over `d` of the first factor is
less than `2 n^{1/4}`, the sum over `0 ≤ j ≤ J` of the second is less than `3 J`, and
`J < 3 log n`. Hence the oscillation is at most `Λ · 2 n^{1/4} · 9 log n`, and
`A_*(ι) - 1/4 = a_mx(ι)`.

## Main results

* `CollatzPosDens.oscillation_subMass_shRetained_le`: the oscillation bound.

## Implementation notes

The submass takes values in `[0, ∞]`; it enters the real-valued oscillation through
`ENNReal.toReal`, and it is finite since retained words have length `n`. The levels `m ≤ n` are
natural numbers, `log` is the natural logarithm `Real.log` and `n^{-a_mx(ι)}` is the real power.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §12.11.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

open Finset

/-- `n ≤ H^{sh}_n`, as `2^n ≤ 3^n ≤ 2^{H^{sh}_n}`. -/
private theorem le_shHeight_self (n : ℕ) : n ≤ shHeight n := by
  by_contra h
  push Not at h
  have h1 := pow_three_le_two_pow_shHeight n
  have h2 : 2 ^ shHeight n < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) h
  have h3 : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by norm_num) n
  omega

/-- The root of the gate bound of `oscillation_subMass_mxShSlice_shRetainedHeads_le` splits into a
factor depending on `d` and a factor depending on `j`. -/
private theorem sqrt_shRetainedHeads_le {n d j : ℕ} (hn : mxGateLevel ≤ n) (hklo : shKLo n ≤ d)
    (hkhi : (d : ℤ) ≤ shKHi n - 1) (hj : j ≤ shJ n) :
    Real.sqrt (((shShellWidth j : ℝ) + 2) * ((2 : ℝ) ^ (shHeight n - 1))⁻¹ *
        #(shRetainedHeads n d j)) ≤
      √(((shHeight n - 1).choose d : ℝ) * (2 : ℝ) ^ (1 - (shHeight n : ℤ))) *
        √(((shShellWidth j : ℝ) + 2) * min 1 ((2 : ℝ) ^ (4 - (j : ℤ)))) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hH : 1 ≤ shHeight n := one_le_shHeight (le_trans one_le_mxGateLevel hn)
  have hpow : ((2 : ℝ) ^ (shHeight n - 1))⁻¹ = (2 : ℝ) ^ (1 - (shHeight n : ℤ)) := by
    rw [← zpow_natCast, ← zpow_neg]
    congr 1
    push_cast [hH]
    ring
  have hcard := card_shRetainedHeads_le hn hklo hkhi hj
  rw [hpow]
  have h0 : 0 ≤ ((shShellWidth j : ℝ) + 2) * (2 : ℝ) ^ (1 - (shHeight n : ℤ)) := by positivity
  calc ((shShellWidth j : ℝ) + 2) * (2 : ℝ) ^ (1 - (shHeight n : ℤ)) * #(shRetainedHeads n d j)
      ≤ ((shShellWidth j : ℝ) + 2) * (2 : ℝ) ^ (1 - (shHeight n : ℤ)) *
          (((shHeight n - 1).choose d : ℝ) * min 1 ((2 : ℝ) ^ (4 - (j : ℤ)))) :=
        mul_le_mul_of_nonneg_left hcard h0
    _ = _ := by ring

/-- **Oscillation of the retained part of the shell cut.** Let `ι` be a Fourier index, `n ≥ n₀`
and `m ≤ n` with `25 n ≤ 27 m`. Then
`Osc_{m,n}(Sub^n_{R^{sh}_n}) ≤ 18 B_F(ι) n^{-a_mx(ι)} log n`. -/
@[collatz_pos_dens "lem_mx_sh_retained_osc"]
theorem oscillation_subMass_shRetained_le (ι : FIndex) {n m : ℕ} (hn : mxGateLevel ≤ n)
    (hmn : m ≤ n) (h25 : 25 * n ≤ 27 * m) :
    oscillation hmn (fun y => (subMass n (shRetained n) y).toReal) ≤
      18 * fourierPrefactor ι * (n : ℝ) ^ (-(amix ι : ℝ)) * Real.log n := by
  have hn80 : 2 ^ 80 ≤ n := by rwa [mxGateLevel_def] at hn
  have hn1 : 1 ≤ n := le_trans one_le_mxGateLevel hn
  set H := shHeight n with hH
  set J := shJ n with hJ
  set I := shRetainedIndex n with hI
  set V : ℕ × ℕ → Set Word := fun x => mxShSlice n x.1 x.2 with hV
  have hdisj : (I : Set (ℕ × ℕ)).PairwiseDisjoint V := by
    intro x _ y _ hxy
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    exact fun h => hxy (eq_of_mxShSlice_shRetainedHeads_inter_nonempty h)
  have hlen : ∀ x, V x ⊆ {w : Word | w.length = n} := fun x _ hw => length_of_mem_mxShSlice hw
  have hsum : (fun y => (subMass n (shRetained n) y).toReal) =
      ∑ x ∈ I, fun y => (subMass n (V x) y).toReal := by
    funext y
    rw [Finset.sum_apply, shRetained_eq_biUnion_shRetainedIndex, subMass_biUnion_finset n I hdisj,
      ENNReal.toReal_sum fun x _ => subMass_ne_top_of_subset_length n (hlen x) y]
  set Λ : ℝ := fourierPrefactor ι * (n : ℝ) ^ (-(Aexp ι : ℝ)) with hΛ
  set f : ℕ → ℝ := fun d => √(((H - 1).choose d : ℝ) * (2 : ℝ) ^ (1 - (H : ℤ))) with hf
  set g : ℕ → ℝ := fun j => √(((shShellWidth j : ℝ) + 2) * min 1 ((2 : ℝ) ^ (4 - (j : ℤ))))
    with hg
  have hΛ0 : 0 ≤ Λ := mul_nonneg (fourierPrefactor_nonneg ι) (by positivity)
  have hterm : ∀ x ∈ I, oscillation hmn (fun y => (subMass n (V x) y).toReal) ≤
      Λ * (f x.1 * g x.2) := by
    rintro ⟨d, j⟩ hx
    obtain ⟨-, hklo, hkhi, hj⟩ := mem_shRetainedIndex.1 hx
    have hd1 : 1 ≤ d := by have := one_le_shKLo hn; omega
    exact (oscillation_subMass_mxShSlice_shRetainedHeads_le ι hn hmn h25 hd1 hkhi j).trans
      (mul_le_mul_of_nonneg_left (sqrt_shRetainedHeads_le hn hklo hkhi hj) hΛ0)
  have hIsub : I ⊆ range n ×ˢ range (J + 1) := filter_subset _ _
  have hfsum : ∑ d ∈ range n, f d < 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    refine lt_of_le_of_lt ?_ (sum_range_sqrt_choose_shHeight_lt hn)
    exact Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (le_shHeight_self n))
      fun _ _ _ => Real.sqrt_nonneg _
  have hJ160 : 4 ≤ J := by
    have h80 : (80 : ℝ) ≤ Real.logb 2 n := by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hn1)]
      exact_mod_cast hn80
    have := le_shJ n
    have : (4 : ℝ) ≤ J := by linarith
    exact_mod_cast this
  have hgsum : ∑ j ∈ range (J + 1), g j < 3 * J := sum_sqrt_shShellWidth_lt hJ160
  have hJ3 : (J : ℝ) + 1 < 3 * Real.log n := shJ_add_one_lt_three_mul_log hn
  have htot : ∑ x ∈ I, f x.1 * g x.2 ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) * (9 * Real.log n) := by
    calc ∑ x ∈ I, f x.1 * g x.2
        ≤ ∑ x ∈ range n ×ˢ range (J + 1), f x.1 * g x.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hIsub fun _ _ _ =>
            mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (∑ d ∈ range n, f d) * ∑ j ∈ range (J + 1), g j := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) * (9 * Real.log n) := by
          apply mul_le_mul hfsum.le _ (sum_nonneg fun _ _ => Real.sqrt_nonneg _) (by positivity)
          linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hexp : (n : ℝ) ^ (-(Aexp ι : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 4) =
      (n : ℝ) ^ (-(amix ι : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    rw [amix_eq_Aexp_sub]
    push_cast
    ring
  rw [hsum]
  calc oscillation hmn (∑ x ∈ I, fun y => (subMass n (V x) y).toReal)
      ≤ ∑ x ∈ I, oscillation hmn (fun y => (subMass n (V x) y).toReal) :=
        oscillation_sum_le hmn I _
    _ ≤ ∑ x ∈ I, Λ * (f x.1 * g x.2) := Finset.sum_le_sum hterm
    _ = Λ * ∑ x ∈ I, f x.1 * g x.2 := by rw [Finset.mul_sum]
    _ ≤ Λ * (2 * (n : ℝ) ^ ((1 : ℝ) / 4) * (9 * Real.log n)) :=
        mul_le_mul_of_nonneg_left htot hΛ0
    _ = 18 * fourierPrefactor ι * ((n : ℝ) ^ (-(Aexp ι : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 4)) *
          Real.log n := by rw [hΛ]; ring
    _ = _ := by rw [hexp]

end CollatzPosDens
