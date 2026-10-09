/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Seed.Histogram
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.LiftedTransfer
public import CollatzPosDens.Transfer.FiberSource

/-!
# The increment identity for `Z_n`

Let `M` be an odd positive integer, `n ≥ 5` and `Q = h_{b_n} + k_{n+1}`. On `G_Q` put
`f_n = ∑_{w ∈ 𝒞(b_n, K_n)} 𝒯_{w,Q} ρ_{k_{n+1}} - ρ_{k_n} ∘ π_{Q,k_n}`. Then the increment of
the weighted central sum is the pairing of `f_n` with the residue histogram:
`Z_{n+1}(M) - Z_n(M) = ∑_{y ∈ G_Q} Hg_{n,Q}(y) f_n(y)`.

Since `n ≥ 5`, the selector condition defining `𝔗_{n+1}` and `𝔗_n` is the same condition on the
first five entries, so a central history of generation `n + 1` is a central history `h` of
generation `n` followed by a word `w ∈ 𝒞(b_n, K_n)` admissible from the endpoint `R_h`, with
endpoint `src(w, R_h)` and weight `ω(h) ω(w)`. Evaluating the lifted transfer at the integer
point `[R_h]_Q` gives `ω(w) [w admissible from R_h] ρ_{k_{n+1}}(src(w, R_h))`, so both
`Z_{n+1}(M)` and `Z_n(M)` are sums over `h ∈ 𝓗_n(M)` of `ω(h)` times a function of
`R_h mod 3^Q`; grouping the histories by this residue gives the histogram.

## Main definitions

* `CollatzPosDens.centralIncrementDensity n`: the function `f_n : G_Q → ℝ`.

## Main results

* `CollatzPosDens.weightedCentralSum_succ_sub`:
  `Z_{n+1}(M) - Z_n(M) = ∑_y Hg_{n,Q}(y) f_n(y)` for `n ≥ 5`.
* `CollatzPosDens.weightedCentralSum_succ_sub_sum_residueHistogram_mul`: pairing a
  function with the histogram is a sum over the central histories.

## Implementation notes

The lifted transfer `𝒯_{w,Q}` needs the bound `|w| + k_{n+1} ≤ Q`, which holds for every
`w ∈ 𝒞(b_n, K_n)` since `|w| ≤ h_{b_n}`; `f_n` is written with this bound as a condition, the
term being `0` when it fails, which never happens on `𝒞(b_n, K_n)`. The sum over
`𝒞(b_n, K_n)` is a `finsum` over this finite set. The identity holds for every integer `M`,
without oddness or positivity, and is stated so.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The reduction level `k_n` is at most `Q = h_{b_n} + k_{n+1}`. -/
theorem centralIncrementDensity_level_le (n : ℕ) :
    level n ≤ hb (scale n) + level (n + 1) := by
  have h1 := four_mul_level_le n
  have h2 := le_hb (scale n)
  omega

/-- The function `f_n = ∑_{w ∈ 𝒞(b_n, K_n)} 𝒯_{w,Q} ρ_{k_{n+1}} - ρ_{k_n} ∘ π_{Q,k_n}` on `G_Q`,
`Q = h_{b_n} + k_{n+1}`. The lifted transfer is taken when `|w| + k_{n+1} ≤ Q`, which holds on
`𝒞(b_n, K_n)`. -/
@[collatz_pos_dens "lem_Zn_increment_identity"]
noncomputable def centralIncrementDensity (n : ℕ)
    (y : ResidueGroup (hb (scale n) + level (n + 1))) : ℝ :=
  (∑ᶠ w ∈ centralFamily (scale n) (cap n),
      if h : w.length + level (n + 1) ≤ hb (scale n) + level (n + 1) then
        liftedTransfer w h (refDensity (level (n + 1))) y
      else 0) -
    refDensity (level n) (residueReduction (centralIncrementDensity_level_le n) y)

section

variable {n : ℕ}

private lemma historyEndpoint_succ (M : ℚ) (h : Fin (n + 1) → Word) :
    historyEndpoint M h = src (h (Fin.last n)) (historyEndpoint M (Fin.init h)) := by
  rw [historyEndpoint_eq_src, historyEndpoint_eq_src, concatWord_succ, src_append]
  rfl

private lemma mem_centralHistories_succ (hn : 5 ≤ n) {M : ℚ} {h : Fin (n + 1) → Word} :
    h ∈ centralHistories M (n + 1) ↔ Fin.init h ∈ centralHistories M n ∧
      h (Fin.last n) ∈ centralFamily (scale n) (cap n) ∧
      Admissible (historyEndpoint M (Fin.init h)) (h (Fin.last n)) := by
  simp only [mem_centralHistories, mem_selectedTuples, concatWord_succ h,
    admissible_append, Fin.forall_fin_succ', historyEndpoint_eq_src]
  simp only [Fin.init, Fin.val_castSucc, Fin.val_last]
  have e1 : (∀ _ : 5 ≤ n + 1, fiveBlockSelector (h ⟨0, by omega⟩) (h ⟨1, by omega⟩)
      (h ⟨2, by omega⟩) (h ⟨3, by omega⟩) (h ⟨4, by omega⟩)) ↔
      fiveBlockSelector (h ⟨0, by omega⟩) (h ⟨1, by omega⟩)
      (h ⟨2, by omega⟩) (h ⟨3, by omega⟩) (h ⟨4, by omega⟩) :=
    ⟨fun H => H (by omega), fun H _ => H⟩
  have e2 : (∀ _ : 5 ≤ n, fiveBlockSelector (h (Fin.castSucc ⟨0, by omega⟩))
      (h (Fin.castSucc ⟨1, by omega⟩)) (h (Fin.castSucc ⟨2, by omega⟩))
      (h (Fin.castSucc ⟨3, by omega⟩)) (h (Fin.castSucc ⟨4, by omega⟩))) ↔
      fiveBlockSelector (h ⟨0, by omega⟩) (h ⟨1, by omega⟩)
      (h ⟨2, by omega⟩) (h ⟨3, by omega⟩) (h ⟨4, by omega⟩) :=
    ⟨fun H => H hn, fun H _ => H⟩
  rw [e1, e2]
  tauto

/-- The endpoint of a central history from an integer is an integer. -/
private lemma intCast_num_historyEndpoint {M : ℤ} {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) :
    ((historyEndpoint M h).num : ℚ) = historyEndpoint M h := by
  refine Rat.coe_int_num_of_den_eq_one ?_
  rw [historyEndpoint_eq_src]
  exact hh.2.den_src_eq_one

/-- Pairing a function with the histogram groups the histories by endpoint residue. -/
theorem weightedCentralSum_succ_sub_sum_residueHistogram_mul (M : ℤ) (n q : ℕ)
    (φ : ResidueGroup q → ℝ) :
    ∑ y, residueHistogram M n q y * φ y =
      ∑ h ∈ (centralHistories_finite M n).toFinset,
        ((concatWord h).weight : ℝ) * φ ((historyEndpoint M h).num : ResidueGroup q) := by
  classical
  have key : ∀ y, residueHistogram M n q y =
      ∑ h ∈ (centralHistories_finite M n).toFinset with
        ((historyEndpoint M h).num : ResidueGroup q) = y, ((concatWord h).weight : ℝ) := by
    intro y
    rw [residueHistogram_eq_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext h
    simp only [mem_filter, Set.Finite.mem_toFinset]
    refine and_congr_right fun hh =>
      ⟨?_, fun hy => ⟨_, intCast_num_historyEndpoint hh, hy⟩⟩
    rintro ⟨r, hr, rfl⟩
    rw [← intCast_num_historyEndpoint hh] at hr
    rw [show r = (historyEndpoint M h).num by exact_mod_cast hr]
  simp only [key, sum_mul]
  rw [← Finset.sum_fiberwise (centralHistories_finite M n).toFinset
    (fun h => ((historyEndpoint M h).num : ResidueGroup q))]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun h hh => ?_
  rw [(mem_filter.1 hh).2]

end

/-- **Increment identity.** For an integer `M` (in the source, odd and positive), `n ≥ 5` and
`Q = h_{b_n} + k_{n+1}`: `Z_{n+1}(M) - Z_n(M) = ∑_{y ∈ G_Q} Hg_{n,Q}(y) f_n(y)`. -/
@[collatz_pos_dens "lem_Zn_increment_identity"]
theorem weightedCentralSum_succ_sub (M : ℤ) {n : ℕ} (hn : 5 ≤ n) :
    weightedCentralSum (n + 1) M - weightedCentralSum n M =
      ∑ y, residueHistogram M n (hb (scale n) + level (n + 1)) y *
        centralIncrementDensity n y := by
  classical
  set Q := hb (scale n) + level (n + 1)
  have hC := centralFamily_finite (scale n) (cap n)
  set H := (centralHistories_finite (M : ℚ) n).toFinset
  have hf : ∀ h ∈ H, centralIncrementDensity n ((historyEndpoint M h).num : ResidueGroup Q) =
      (∑ w ∈ hC.toFinset, if Admissible (historyEndpoint M h) w then
          (w.weight : ℝ) * refDensity (level (n + 1))
            ((src w (historyEndpoint M h)).num : ResidueGroup (level (n + 1)))
        else 0) -
        refDensity (level n) ((historyEndpoint M h).num : ResidueGroup (level n)) := by
    intro h hh
    rw [Set.Finite.mem_toFinset] at hh
    rw [centralIncrementDensity, finsum_mem_eq_finite_toFinset_sum _ hC,
      residueReduction_intCast]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Set.Finite.mem_toFinset] at hw
    have hlen : w.length + level (n + 1) ≤ Q := by
      have := length_le_hb_of_mem_firstCrossing (centralFamily_subset_firstCrossing _ _ hw)
      omega
    rw [dite_eq_left_of_eq_true (eq_true hlen), liftedTransfer_intCast,
      intCast_num_historyEndpoint hh]
  rw [weightedCentralSum_succ_sub_sum_residueHistogram_mul,
    Finset.sum_congr rfl fun h hh => by rw [hf h hh]]
  simp only [mul_sub, sum_sub_distrib]
  congr 1
  · rw [weightedCentralSum_eq_sum]
    simp only [mul_sum, mul_ite, mul_zero]
    rw [← Finset.sum_product' (f := fun h w => if Admissible (historyEndpoint M h) w then
        ((concatWord h).weight : ℝ) * ((w.weight : ℝ) * refDensity (level (n + 1))
          ((src w (historyEndpoint M h)).num : ResidueGroup (level (n + 1)))) else 0),
      ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun h => (Fin.init h, h (Fin.last n)))
      (fun p => Fin.snoc p.1 p.2) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      rw [Set.Finite.mem_toFinset] at hh
      obtain ⟨h1, h2, h3⟩ := (mem_centralHistories_succ hn).1 hh
      simp only [mem_filter, mem_product, Set.Finite.mem_toFinset]
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨h, w⟩ hp
      simp only [mem_filter, mem_product, Set.Finite.mem_toFinset] at hp ⊢
      refine (mem_centralHistories_succ hn).2 ?_
      simpa only [Fin.init_snoc, Fin.snoc_last] using ⟨hp.1.1, hp.1.2, hp.2⟩
    · intro h _
      simp
    · rintro ⟨h, w⟩ _
      simp
    · intro h _
      dsimp only
      rw [show concatWord h = concatWord (Fin.init h) ++ h (Fin.last n) from concatWord_succ h,
        Word.weight_append, historyEndpoint_succ]
      push_cast
      ring
  · rw [weightedCentralSum_eq_sum]

end CollatzPosDens
