/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FiniteTransfer.TransferEstimate
public import CollatzPosDens.FirstCrossing.DeficitFamily
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.LevelLateLower
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Recipe.PhHhist
public import CollatzPosDens.Seed.PairingSharp
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.MarkedMassUnfiltered
public import CollatzPosDens.Terminal.ShiftCount
public import CollatzPosDens.Terminal.ShiftRange
public import CollatzPosDens.Transfer.FiberSource
public import CollatzPosDens.Transfer.MxProfile
public import CollatzPosDens.Transfer.PrefixExtension

/-!
# The error of the unfiltered marked mass

Let `t ≥ t_min` (`t_min = targetFloor`) be an odd integer, `j ≥ J_c` (`J_c = covGen`) and `X`
admissible for generation `j`. Then
$$\bigl|\Theta^{\circ}_{j,X}(t) - Z_j(t)\bigr|
  \le 5\,j^{9/2}\, \mathsf g^{j/2} \Bigl(2\,\mathfrak M_{\mathrm o}(k_j) + \frac{2^{116}}{b_j^{6}}
    + 2^{-(K_j+1)}\Bigr),$$
where `𝔐_o` is the mixing profile at the original Fourier index `o`.

Write `b = b_j`, `k = k_j` and `Q = h_b + k`. For a shift `u` let
$$f_u = \sum_{w \in \mathcal W(b, u, K_j)} \mathcal T_{w,Q}\,\rho_k - \rho_k \circ \pi_{Q,k}
  \quad\text{on } G_Q.$$
Evaluating the lifted transfers at the endpoint `R_h` of a central history `h` through the
fiber of a residue map gives
$\Theta^{\circ}_{j,X}(t) - Z_j(t)
  = \sum_{h \in \mathcal H_j(t)} \omega(h)\, f_{u_h}(R_h \bmod 3^Q)$.
For each of the fewer than `j^2/82` shifts `u`, the finite-transfer estimate at the index `o`
and the deficit of a full first-crossing family give
`⟨|f_u|⟩_Q ≤ 2 𝔐_o(k) + 2^{116}/b^6 + 2^{-(K_j+1)}`, and the sharp pairing estimate bounds
the histories with shift `u` by `𝓗_hist j^{5/2} 𝗀^{j/2}` times this, with `𝓗_hist = 344`
(it applies as `N_* ≤ J_c ≤ j`). Summing over the shifts and using `344/82 ≤ 5` gives the
claim.

## Main results

* `CollatzPosDens.sum_attach_liftedTransfer_intCast`: the sum of the lifted transfers over a
  finite family, evaluated at the reduction of an integer `R`.
* `CollatzPosDens.one_sub_toReal_geomMass_firstCrossing_le`: the deficit of a full
  first-crossing family, as a real number.
* `CollatzPosDens.abs_markedMassUnfiltered_sub_weightedCentralSum_le`: the estimate.

## Implementation notes

The powers `j^{9/2}` and `𝗀^{j/2}` are real powers. The seed `t` is an integer, cast to `ℚ` to
be fed to `Θ°` and `Z_j`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace CollatzPosDens

/-- The sum of the lifted transfers `𝒯_{w,Q} g` over a finite family `𝒱` of words of length at
most `d`, evaluated at the reduction `[R]_{d+k}` of an integer `R`, is the sum of
`ω(w) g([src(w, R)]_k)` over the words of `𝒱` admissible from `R`. -/
theorem sum_attach_liftedTransfer_intCast {V : Finset Word} {d k : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ d) (g : ResidueGroup k → ℝ) (R : ℤ) :
    ∑ w ∈ V.attach, liftedTransfer w.1 (Nat.add_le_add_right (hlen w.1 w.2) k) g
        (R : ResidueGroup (d + k)) =
      ∑ w ∈ V with Admissible (R : ℚ) w, (w.weight : ℝ) * g ((src w R).num : ResidueGroup k) := by
  rw [sum_filter]
  simp only [liftedTransfer_intCast]
  exact sum_attach V fun w =>
    if Admissible (R : ℚ) w then (w.weight : ℝ) * g ((src w R).num : ResidueGroup k) else 0


/-- The deficit `1 - 𝐩(𝒲(b, u, K))` of a full first-crossing family, as a real number, is at most
`2^{116}/b^6 + 2^{-(K+1)}` for `b ≥ 1` and `0 ≤ u ≤ 2 r_b`. -/
theorem one_sub_toReal_geomMass_firstCrossing_le {b : ℕ} (hb0 : 0 < b) {u : ℤ} (hu0 : 0 ≤ u)
    (hu : u ≤ 2 * rb b) (K : ℕ) :
    1 - (geomMass (firstCrossing b u K)).toReal ≤ 2 ^ 116 / (b : ℝ) ^ 6 + 2⁻¹ ^ (K + 1) := by
  have hle1 : geomMass (firstCrossing b u K) ≤ 1 := by
    have hfin := firstCrossing_finite b u K
    have := geomMass_le_one_of_isPrefixFree (V := (hfin.toFinset : Set Word))
      (by rw [Set.Finite.coe_toFinset]; exact isPrefixFree_firstCrossing _ _ _)
      (h := hb b)
      (fun w hw => length_le_hb_of_mem_firstCrossing ((Set.Finite.mem_toFinset _).1 hw))
    rwa [Set.Finite.coe_toFinset] at this
  have hne : (2 : ℝ≥0∞) ^ 116 / (b : ℝ≥0∞) ^ 6 + 2⁻¹ ^ (K + 1) ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (by simp) ?_, by simp⟩
    exact pow_ne_zero _ (by exact_mod_cast hb0.ne')
  rw [← ENNReal.toReal_one, ← ENNReal.toReal_sub_of_le hle1 ENNReal.one_ne_top]
  refine (ENNReal.toReal_mono hne (one_sub_geomMass_firstCrossing_le b hu0 hu K)).trans_eq ?_
  rw [ENNReal.toReal_add (ENNReal.div_ne_top (by simp)
      (pow_ne_zero _ (by exact_mod_cast hb0.ne'))) (by simp),
    ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_inv]
  simp

/-- The error of the unfiltered marked mass: for an odd integer `t ≥ t_min`, `j ≥ J_c` and `X`
admissible for generation `j`,
`|Θ°_{j,X}(t) - Z_j(t)| ≤ 5 j^{9/2} 𝗀^{j/2} (2 𝔐_o(k_j) + 2^{116}/b_j^6 + 2^{-(K_j+1)})`,
where `𝔐_o` is the mixing profile at the original Fourier index `o`. -/
@[collatz_pos_dens "lem_s06_unfiltered_error"]
theorem abs_markedMassUnfiltered_sub_weightedCentralSum_le {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) {j : ℕ} (hj : covGen ≤ j) {X : ℝ}
    (hX : IsAdmissibleScale t j X) :
    |markedMassUnfiltered j X t - weightedCentralSum j t| ≤
      5 * (j : ℝ) ^ (9 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
        (2 * mxProfile .o (level j) + 2 ^ 116 / (scale j : ℝ) ^ 6 + 2⁻¹ ^ (cap j + 1)) := by
  classical
  set b := scale j with hbdef
  set k := level j with hkdef
  set Q := hb b + k with hQ
  have hkQ : k ≤ Q := Nat.le_add_left _ _
  have hjN : generationThreshold ≤ j := selEnd_le_generationThreshold_range.2.trans hj
  have hlate := level_late_lower hjN
  have hk0 : mxGateLevel ≤ k := by
    have := (le_max_left _ _).trans hlate
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ k := by
    have h47 := (le_max_right _ _).trans hlate
    have hg1 : (1 : ℝ) ≤ (growthRatio : ℝ) ^ j := one_le_pow₀ one_lt_growthRatio_cast.le
    rw [← hkdef] at h47
    linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) (sixteen544_le_scale j)
  have hQb : Q ≤ 2 * scale j := by
    have := hb_eq b
    have := level_def j
    omega
  set ε : ℝ := 2 * mxProfile .o k + 2 ^ 116 / (b : ℝ) ^ 6 + 2⁻¹ ^ (cap j + 1) with hε
  have hε0 : 0 ≤ ε := by
    have := mxProfile_pos .o hk1
    positivity
  set H := centralHistories (t : ℚ) j with hH
  have hHfin : H.Finite := centralHistories_finite (t : ℚ) j
  have htpos : 0 < t := lt_of_lt_of_le (by exact_mod_cast targetFloor_pos) ht
  let V : ℕ → Finset Word := fun s => (firstCrossing_finite b s (cap j)).toFinset
  have hlen : ∀ s, ∀ w ∈ V s, w.length ≤ hb b := fun s w hw =>
    length_le_hb_of_mem_firstCrossing ((Set.Finite.mem_toFinset _).1 hw)
  let f : ℕ → ResidueGroup Q → ℝ := fun s y =>
    ∑ w ∈ (V s).attach, liftedTransfer w.1 (Nat.add_le_add_right (hlen s w.1 w.2) k)
      (refDensity k) y - refDensity k (residueReduction hkQ y)
  let u : (Fin j → Word) → ℕ := historyShift j X t
  let r : (Fin j → Word) → ResidueGroup Q := fun h =>
    ((historyEndpoint (t : ℚ) h).num : ResidueGroup Q)
  have hstep1 : markedMassUnfiltered j X t - weightedCentralSum j t =
      ∑ h ∈ hHfin.toFinset, ((concatWord h).weight : ℝ) * f (u h) (r h) := by
    rw [markedMassUnfiltered_eq_sum, weightedCentralSum_eq_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun h hh => ?_
    rw [Set.Finite.mem_toFinset] at hh
    obtain ⟨m, hm, -, -⟩ := historyEndpointAt_large hodd ht hh le_rfl
    have hm' : historyEndpoint (t : ℚ) h = m := hm
    rw [← mul_sub]
    refine congrArg (fun x => ((concatWord h).weight : ℝ) * x) ?_
    simp only [f, r, hm', Rat.num_intCast]
    rw [sum_attach_liftedTransfer_intCast (hlen _), residueReduction_intCast]
    refine congrArg (· - _) ?_
    refine sum_congr ?_ fun _ _ => rfl
    ext w
    simp [mem_markedMassUnfilteredWords, V, u, hm', hbdef]
  set B : ℝ := 344 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) * ε with hB
  have hstep2 : ∀ h₀ ∈ H, ∑ h ∈ hHfin.toFinset with u h = u h₀,
      ((concatWord h).weight : ℝ) * |f (u h₀) (r h)| ≤ B := by
    intro h₀ hh₀
    obtain ⟨hu0, hu1⟩ := hX.historyShift_mem_Icc hh₀
    have hcoe : ((V (u h₀) : Set Word)) = firstCrossing b (u h₀) (cap j) :=
      Set.Finite.coe_toFinset _
    have hpf : InformationTheory.IsPrefixFree ((V (u h₀) : Set Word)) := by
      rw [hcoe]
      exact isPrefixFree_firstCrossing b (u h₀) (cap j)
    have hTE := residueAvg_abs_sum_liftedTransfer_refDensity_sub_le .o hpf hk0 (hlen (u h₀)) hk0 hkQ
    have hD : 1 - (geomMass (V (u h₀) : Set Word)).toReal ≤
        2 ^ 116 / (b : ℝ) ^ 6 + 2⁻¹ ^ (cap j + 1) := by
      rw [hcoe]
      exact one_sub_toReal_geomMass_firstCrossing_le hb0 hu0 hu1 (cap j)
    have havg : residueAvg Q (fun y => |f (u h₀) y|) ≤ ε := by
      refine hTE.trans ?_
      rw [hε]
      linarith
    have hP := finsum_weight_mul_abs_le_Hhist hodd htpos hjN hQb
      (H' := {h ∈ H | u h = u h₀}) (fun h hh => hh.1) (f (u h₀))
    rw [finsum_mem_eq_finite_toFinset_sum _ (hHfin.subset fun h hh => hh.1)] at hP
    have hset : hHfin.toFinset.filter (fun h => u h = u h₀) =
        (hHfin.subset fun h (hh : h ∈ {h ∈ H | u h = u h₀}) => hh.1).toFinset := by
      ext h
      simp
    rw [hset]
    refine hP.trans ?_
    have hg0 := growthRatio_cast_pos
    have hJ : 0 ≤ (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) := by positivity
    have hA : 0 ≤ (Hhist : ℝ) * (j : ℝ) ^ (5 / 2 : ℝ) *
        (growthRatio : ℝ) ^ ((j : ℝ) / 2) := by rw [Hhist_cast]; positivity
    refine (mul_le_mul_of_nonneg_left havg hA).trans_eq ?_
    rw [hB, Hhist_cast]
  obtain ⟨hUfin, hUcard⟩ := ncard_historyShift_image_lt (j := j) hj X hodd ht
  have hmaps : ∀ h ∈ hHfin.toFinset, u h ∈ hUfin.toFinset := fun h hh => by
    rw [Set.Finite.mem_toFinset] at hh ⊢
    exact ⟨h, hh, rfl⟩
  have hg0 := growthRatio_cast_pos
  have hBnn : 0 ≤ B := by positivity
  calc |markedMassUnfiltered j X t - weightedCentralSum j t|
      ≤ ∑ h ∈ hHfin.toFinset, ((concatWord h).weight : ℝ) * |f (u h) (r h)| := by
        rw [hstep1]
        refine (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun h _ => ?_)
        rw [abs_mul, abs_of_nonneg (by exact_mod_cast (Word.weight_pos _).le)]
    _ = ∑ s ∈ hUfin.toFinset, ∑ h ∈ hHfin.toFinset with u h = s,
          ((concatWord h).weight : ℝ) * |f (u h) (r h)| :=
        (sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ s ∈ hUfin.toFinset, B := by
        refine sum_le_sum fun s hs => ?_
        rw [Set.Finite.mem_toFinset] at hs
        obtain ⟨h₀, hh₀, rfl⟩ := hs
        calc _ = ∑ h ∈ hHfin.toFinset with u h = u h₀,
              ((concatWord h).weight : ℝ) * |f (u h₀) (r h)| :=
              sum_congr rfl fun h hh => by rw [(mem_filter.1 hh).2]
          _ ≤ B := hstep2 h₀ hh₀
    _ = (historyShift j X t '' H).ncard * B := by
        rw [sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card _ hUfin]
    _ ≤ (j : ℝ) ^ 2 / 82 * B := mul_le_mul_of_nonneg_right hUcard.le hBnn
    _ = 344 / 82 * ((j : ℝ) ^ 2 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
          ε) := by rw [hB]; ring
    _ ≤ 5 * ((j : ℝ) ^ 2 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
          ε) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by
        have hj0 : (0 : ℝ) < j :=
          Nat.cast_pos.mpr (lt_of_lt_of_le (by rw [covGen_def]; norm_num) hj)
        have he : (j : ℝ) ^ 2 * (j : ℝ) ^ (5 / 2 : ℝ) = (j : ℝ) ^ (9 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hj0]
          norm_num
        rw [← he]
        ring

end CollatzPosDens
