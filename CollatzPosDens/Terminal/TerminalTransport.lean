/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Wb
public import CollatzPosDens.Transfer.FiberSource
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Transfer.PrefixExtension
public import CollatzPosDens.Transfer.LiftedTransfer
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.InverseOrbitOdd
public import CollatzPosDens.FirstCrossing.BracketDecay
public import CollatzPosDens.FirstCrossing.DeficitFamily
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.FullLossRate
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.LevelGate
public import CollatzPosDens.FiniteTransfer.TransferEstimate
public import CollatzPosDens.Recipe.F
public import CollatzPosDens.Recipe.Growth
public import CollatzPosDens.Recipe.Varrho
public import CollatzPosDens.Recipe.Varsigma
public import CollatzPosDens.Seed.Histogram
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Pairing
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.MarkedMassUnfiltered
public import CollatzPosDens.Terminal.ShiftCount
public import CollatzPosDens.Terminal.ShiftRange
public import CollatzPosDens.Transfer.MixingConst

/-!
# Terminal transport error

Let `M ≥ 16^{b_0}` be an odd integer, `n ≥ 9200000`, and let `X` be admissible for generation
`n`. Then the unfiltered marked mass and the weighted central sum are close:
$$\bigl|\Theta^{\circ}_{n,X}(M) - Z_n(M)\bigr| \le F\, n^{9/2} \varrho^n.$$

Write `b = b_n`, `k = k_n` and `Q = h_b + k ≤ 2b`; the level gate gives `k ≥ 2^{131072}`.
For each shift `u` let `f_u = ∑_{w ∈ 𝒲(b, u, K_n)} 𝒯_{w,Q} ρ_k - ρ_k ∘ π_{Q,k}` on `G_Q`.
Evaluating a transfer at an integer point gives
`Θ°_{n,X}(M) - Z_n(M) = ∑_h ω(h) f_{u_h}(R_h mod 3^Q)`. Grouping the histories by their shift,
the pairing estimate bounds each group by `Π_n ⟨|f_u|⟩_Q` with
`Π_n = (4075/56)(277/128) n^{5/2} 𝖦^n`. Since `0 ≤ u ≤ 2 r_b`, the finite-transfer estimate,
the deficit of a full first-crossing family, the decay of the full-family loss and the bracket
decay give `⟨|f_u|⟩_Q < (2/3)(28/1000)(C+1) ς^n`. There are fewer than `n^2/56` shifts, and
`𝖦 ς = ϱ`, `(1/56)(4075/56)(277/128)(2/3)(28/1000) < 3`, `F = 3 (C + 1)`.

## Main results

* `CollatzPosDens.abs_markedMassUnfiltered_sub_weightedCentralSum_le`: the transport
  bound `|Θ°_{n,X}(M) - Z_n(M)| ≤ F n^{9/2} ϱ^n`.

## Implementation notes

The endpoint `R_h` is a rational number, an integer for `h ∈ 𝓗_n(M)`; its residue is read as
that of its numerator, as in `CollatzPosDens.weightedCentralSum`. The power `n^{9/2}` is
the real power `(n : ℝ) ^ (9 / 2 : ℝ)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §18.
-/

@[expose] public section

open scoped ENNReal
open Finset

namespace CollatzPosDens

/-- `Q = h_{b_n} + k_n ≤ 2 b_n`. -/
private theorem terminalTransport_modulus_le (n : ℕ) :
    hb (scale n) + level n ≤ 2 * scale n := by
  have := five_mul_wb_le (scale n)
  have := four_mul_level_le n
  rw [hb_def]
  omega

/-- The first-crossing words at scale `b_n`, shift `u` and cap `K_n`, as a `Finset`. -/
private noncomputable abbrev terminalTransportWords (n u : ℕ) : Finset Word :=
  (firstCrossing_finite (scale n) u (cap n)).toFinset

private theorem terminalTransportWords_length_le {n u : ℕ} {w : Word}
    (hw : w ∈ terminalTransportWords n u) : w.length ≤ hb (scale n) :=
  length_le_hb_of_mem_firstCrossing ((Set.Finite.mem_toFinset _).1 hw)

private theorem terminalTransportWords_isPrefixFree (n u : ℕ) :
    InformationTheory.IsPrefixFree ((terminalTransportWords n u : Finset Word) : Set Word) := by
  rw [Set.Finite.coe_toFinset]
  exact isPrefixFree_firstCrossing _ _ _

/-- The defect `f_u = ∑_{w ∈ 𝒲(b_n, u, K_n)} 𝒯_{w,Q} ρ_k - ρ_k ∘ π_{Q,k}` on `G_Q`, where
`k = k_n` and `Q = h_{b_n} + k_n`. -/
private noncomputable def terminalTransportDefect (n u : ℕ)
    (y : ResidueGroup (hb (scale n) + level n)) : ℝ :=
  ∑ w ∈ (terminalTransportWords n u).attach,
      liftedTransfer w.1 (Nat.add_le_add_right (terminalTransportWords_length_le w.2) (level n))
        (refDensity (level n)) y -
    refDensity (level n) (residueReduction (Nat.le_add_left (level n) (hb (scale n))) y)

/-- At the residue of an integer `m`, the defect is the transported mass minus the reference
density. -/
private theorem terminalTransportDefect_intCast (n u : ℕ) (m : ℤ) :
    terminalTransportDefect n u (m : ResidueGroup (hb (scale n) + level n)) =
      (∑ᶠ w ∈ {w | w ∈ firstCrossing (scale n) u (cap n) ∧ Admissible (m : ℚ) w},
          (w.weight : ℝ) * refDensity (level n) ((src w m).num : ResidueGroup (level n))) -
        refDensity (level n) (((m : ℚ).num : ℤ) : ResidueGroup (level n)) := by
  classical
  rw [terminalTransportDefect, Rat.num_intCast, residueReduction_intCast]
  congr 1
  have hset : {w | w ∈ firstCrossing (scale n) u (cap n) ∧ Admissible (m : ℚ) w} =
      ↑((terminalTransportWords n u).filter fun w => Admissible (m : ℚ) w) := by
    ext w
    simp [terminalTransportWords]
  rw [hset, finsum_mem_coe_finset, Finset.sum_filter,
    ← Finset.sum_attach (terminalTransportWords n u)]
  exact Finset.sum_congr rfl fun w _ => by rw [liftedTransfer_intCast]

/-- `Θ°_{n,X}(M) - Z_n(M) = ∑_{h ∈ 𝓗_n(M)} ω(h) f_{u_h}(R_h mod 3^Q)`. -/
private theorem terminalTransport_sub_eq_sum {M : ℤ} (hodd : Odd M) (hM : 0 < M)
    (n : ℕ) (X : ℝ) :
    markedMassUnfiltered n X M - weightedCentralSum n M =
      ∑ h ∈ (centralHistories_finite M n).toFinset,
        ((concatWord h).weight : ℝ) *
          terminalTransportDefect n (historyShift n X M h)
            ((historyEndpoint M h).num : ResidueGroup (hb (scale n) + level n)) := by
  rw [markedMassUnfiltered_eq_sum, weightedCentralSum_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Set.Finite.mem_toFinset] at hh
  obtain ⟨m, hm⟩ := pairing_finsum_weight_mul_abs_le_endpoint_eq_int hodd hM hh
  rw [← mul_sub, ← finsum_mem_eq_finite_toFinset_sum _ (markedMassUnfilteredWords_finite n X M h)]
  congr 1
  simp only [markedMassUnfilteredWords]
  generalize historyShift n X M h = u
  rw [hm, terminalTransportDefect_intCast]
  simp only [Rat.num_intCast]

/-- The deficit `Δ_u = 1 - 𝐩(𝒲(b_n, u, K_n))` satisfies
`0 ≤ Δ_u ≤ (2^{121} + 1024 + 2^{-16}) ς^n` for `0 ≤ u ≤ 2 r_{b_n}`. -/
private theorem terminalTransport_deficit_mem (n u : ℕ)
    (hu : (u : ℤ) ≤ 2 * rb (scale n)) :
    0 ≤ 1 - (geomMass ((terminalTransportWords n u : Finset Word) : Set Word)).toReal ∧
      1 - (geomMass ((terminalTransportWords n u : Finset Word) : Set Word)).toReal ≤
        (2 ^ 121 + 1024 + 2⁻¹ ^ 16) * deficitRate ^ n := by
  have hcoe : ((terminalTransportWords n u : Finset Word) : Set Word) =
      firstCrossing (scale n) u (cap n) := Set.Finite.coe_toFinset _
  have hp := geomMass_coe_finset_ne_top (terminalTransportWords n u)
  have hle1 : geomMass ((terminalTransportWords n u : Finset Word) : Set Word) ≤ 1 :=
    geomMass_le_one_of_isPrefixFree (terminalTransportWords_isPrefixFree n u)
      (fun w hw => terminalTransportWords_length_le hw)
  refine ⟨?_, ?_⟩
  · simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle1
  have hdef := one_sub_geomMass_firstCrossing_le (scale n) (Int.natCast_nonneg u) hu (cap n)
  have hb0 : (scale n : ℝ≥0∞) ^ 6 ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (show 0 < scale n by have := nine_le_scale n; omega).ne')
  have hE1 : (2 : ℝ≥0∞) ^ 140 / (scale n : ℝ≥0∞) ^ 6 ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (by simp)) hb0
  have hE2 : (2⁻¹ : ℝ≥0∞) ^ (cap n + 1) ≠ ∞ := ENNReal.pow_ne_top (by simp)
  rw [← hcoe] at hdef
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hp, ENNReal.add_ne_top.2 ⟨hE1, hE2⟩⟩)
    (tsub_le_iff_left.1 hdef)
  rw [ENNReal.toReal_add hp (ENNReal.add_ne_top.2 ⟨hE1, hE2⟩), ENNReal.toReal_add hE1 hE2,
    ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.toReal_one] at h1
  have hloss := full_loss_rate_le n
  have e1 : (2 : ℝ) ^ (140 : ℕ) * (scale n : ℝ) ^ (-6 : ℤ) = 2 ^ 140 / (scale n : ℝ) ^ 6 := by
    rw [zpow_neg, zpow_ofNat, div_eq_mul_inv]
  have e2 : (2 : ℝ) ^ (-((cap n : ℤ) + 1)) = (2⁻¹ : ℝ) ^ (cap n + 1) := by
    rw [zpow_neg, inv_pow, ← zpow_natCast]
    push_cast
    rfl
  rw [e1, e2, show (2 : ℝ) ^ (-16 : ℤ) = 2⁻¹ ^ 16 by norm_num] at hloss
  have hς : 0 ≤ deficitRate ^ n := pow_nonneg deficitRate_nonneg n
  nlinarith

/-- `⟨|f_u|⟩_Q < (2/3)(28/1000)(C+1) ς^n` for `0 ≤ u ≤ 2 r_{b_n}` and `n ≥ 9200000`. -/
private theorem terminalTransportDefect_residueAvg_lt {n : ℕ} (hn : 9200000 ≤ n) (u : ℕ)
    (hu : (u : ℤ) ≤ 2 * rb (scale n)) :
    residueAvg (hb (scale n) + level n) (fun y => |terminalTransportDefect n u y|) <
      2 / 3 * (28 / 1000 * (mixingConst + 1) * deficitRate ^ n) := by
  have hk := level_gate hn
  have hest := residueAvg_abs_sum_liftedTransfer_refDensity_sub_le
    (terminalTransportWords_isPrefixFree n u) hk
    (fun w hw => terminalTransportWords_length_le hw) hk (Nat.le_add_left (level n) _)
  obtain ⟨hD0, hD⟩ := terminalTransport_deficit_mem n u hu
  have hbr := bracket_decay_lt (by omega : 444 ≤ n) le_rfl le_rfl hD0 hD
  have hkpos : (0 : ℝ) < level n := by exact_mod_cast level_pos n
  have hconv : mixingConst / (level n : ℝ) ^ (9 / 8 : ℝ) =
      mixingConst * (level n : ℝ) ^ (-(9 / 8) : ℝ) := by
    rw [Real.rpow_neg hkpos.le, div_eq_mul_inv]
  rw [hconv] at hest
  refine hest.trans_lt ?_
  have := mul_lt_mul_of_pos_left hbr (by norm_num : (0 : ℝ) < 2 / 3)
  convert this using 2
  ring

/-- The histories with a fixed shift `u` contribute less than
`Π_n · (2/3)(28/1000)(C+1) ς^n`. -/
private theorem terminalTransport_abs_sum_shift_le {M : ℤ} (hodd : Odd M) (hM : 0 < M)
    {n : ℕ} (hn : 9200000 ≤ n) {X : ℝ} (hX : IsAdmissibleScale M n X) {u : ℕ}
    (hu : u ∈ (centralHistories_finite M n).toFinset.image
      (historyShift n X M)) :
    |∑ h ∈ (centralHistories_finite M n).toFinset with
        historyShift n X M h = u,
      ((concatWord h).weight : ℝ) * terminalTransportDefect n (historyShift n X M h)
        ((historyEndpoint M h).num : ResidueGroup (hb (scale n) + level n))| ≤
      4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n *
        (2 / 3 * (28 / 1000 * (mixingConst + 1) * deficitRate ^ n)) := by
  set Hs := (centralHistories_finite M n).toFinset
  obtain ⟨h₀, hh₀, rfl⟩ := Finset.mem_image.1 hu
  rw [Set.Finite.mem_toFinset] at hh₀
  have hrange := (hX.historyShift_mem_Icc hh₀).2
  set u := historyShift n X M h₀
  have hsub : ((Hs.filter fun h => historyShift n X M h = u : Finset _) :
      Set (Fin n → Word)) ⊆ centralHistories M n := fun h hh => by
    simpa [Hs] using (Finset.mem_filter.1 hh).1
  have hpair := pairing_finsum_weight_mul_abs_le hodd hM (by omega : 10000 ≤ n)
    (terminalTransport_modulus_le n) hsub (terminalTransportDefect n u)
  rw [finsum_mem_coe_finset] at hpair
  have hcoef : (0 : ℝ) ≤
      4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n := by
    have := histogramGrowth_pos
    positivity
  calc _ ≤ ∑ h ∈ Hs with historyShift n X M h = u, |((concatWord h).weight : ℝ) *
        terminalTransportDefect n (historyShift n X M h)
          ((historyEndpoint M h).num : ResidueGroup (hb (scale n) + level n))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ h ∈ Hs with historyShift n X M h = u, ((concatWord h).weight : ℝ) *
        |terminalTransportDefect n u
          ((historyEndpoint M h).num : ResidueGroup (hb (scale n) + level n))| := by
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [(Finset.mem_filter.1 hh).2, abs_mul,
          abs_of_pos (by exact_mod_cast Word.weight_pos _)]
    _ ≤ _ := hpair
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (terminalTransportDefect_residueAvg_lt hn u hrange).le hcoef

/-- **Terminal transport error**. Let `M ≥ 16^{b_0}` be an odd integer, `n ≥ 9200000`, and let
`X` be admissible for generation `n`. Then
`|Θ°_{n,X}(M) - Z_n(M)| ≤ F n^{9/2} ϱ^n`. -/
@[collatz_pos_dens "lem_terminal_transport"]
theorem abs_markedMassUnfiltered_sub_weightedCentralSum_le {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) {n : ℕ} (hn : 9200000 ≤ n) {X : ℝ}
    (hX : IsAdmissibleScale M n X) :
    |markedMassUnfiltered n X M - weightedCentralSum n M| ≤
      errorPrefactor * (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n := by
  classical
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  set Hs := (centralHistories_finite M n).toFinset
  set S := Hs.image (historyShift n X M)
  set P : ℝ := 4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n *
    (2 / 3 * (28 / 1000 * (mixingConst + 1) * deficitRate ^ n))
  rw [terminalTransport_sub_eq_sum hodd hM0 n X,
    ← Finset.sum_fiberwise_of_maps_to (g := historyShift n X M) (t := S)
      fun h hh => Finset.mem_image_of_mem _ hh]
  have hcard : (S.card : ℝ) < (n : ℝ) ^ 2 / 56 := by
    have h := (ncard_historyShift_image_lt (by omega : 10000 ≤ n) X hodd hM).2
    have : (historyShift n X M '' centralHistories M n).ncard = S.card := by
      rw [← Set.ncard_coe_finset, Finset.coe_image, Set.Finite.coe_toFinset]
    rwa [this] at h
  have hrate := histogramGrowth_pow_mul_deficitRate_pow n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (n : ℝ) ^ (9 / 2 : ℝ) = (n : ℝ) ^ 2 * (n : ℝ) ^ (5 / 2 : ℝ) := by
    rw [show (9 / 2 : ℝ) = (2 : ℕ) + 5 / 2 by norm_num, Real.rpow_add hnpos,
      Real.rpow_natCast]
  have hP : P = 45151 / 15360 * (mixingConst + 1) * (n : ℝ) ^ (5 / 2 : ℝ) *
      errorDecayRatio ^ n := by
    rw [← hrate]
    simp only [P]
    ring
  have hPnn : 0 ≤ P := by
    rw [hP]
    have := mixingConst_pos
    have := errorDecayRatio_pos
    positivity
  calc _ ≤ ∑ u ∈ S, |∑ h ∈ Hs with historyShift n X M h = u,
        ((concatWord h).weight : ℝ) * terminalTransportDefect n (historyShift n X M h)
          ((historyEndpoint M h).num : ResidueGroup (hb (scale n) + level n))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u ∈ S, P :=
        Finset.sum_le_sum fun _ hu => terminalTransport_abs_sum_shift_le hodd hM0 hn hX hu
    _ = (S.card : ℝ) * P := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ 2 / 56 * P := mul_le_mul_of_nonneg_right hcard.le hPnn
    _ ≤ errorPrefactor * (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n := by
        rw [hP, hpow, errorPrefactor_def]
        have := mixingConst_pos
        have := errorDecayRatio_pos
        have hq : 0 ≤ (mixingConst + 1) * ((n : ℝ) ^ 2 * (n : ℝ) ^ (5 / 2 : ℝ)) *
            errorDecayRatio ^ n := by positivity
        nlinarith

end CollatzPosDens
