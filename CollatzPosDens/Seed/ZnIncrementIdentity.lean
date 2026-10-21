/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.SelEnd
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Seed.Histogram
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05Tuples
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
public import CollatzPosDens.Transfer.S02LiftedTransfer
public import CollatzPosDens.Transfer.FiberSource

/-!
# The increment identity for `Z_n`

Let `t` be an odd positive integer, `n ≥ j_e` (where `j_e = 29` is the selector end `selEnd`)
and `Q = h_{b_n} + k_{n+1}`. On `G_Q` put
`f_n = ∑_{w ∈ 𝒞(b_n, K_n)} 𝒯_{w,Q} ρ_{k_{n+1}} - ρ_{k_n} ∘ π_{Q,k_n}`. Then the increment of
the weighted central sum is the pairing of `f_n` with the residue histogram:
`Z_{n+1}(t) - Z_n(t) = ∑_{y ∈ G_Q} Hg_{n,Q}(y) f_n(y)`, where `Hg_{n,Q}` is the residue
histogram of the central histories `𝓗_n(t)`.

Since `n ≥ j_e`, the selectors defining `𝔗_{n+1}` and `𝔗_n` impose the same conditions,
`off(w_0) ≤ 3/4` and `off(w_i) ≤ M_sel` for `0 < i < j_e`, none of which concerns the last
entry, so a central history of generation `n + 1` is a central history `h` of
generation `n` followed by a word `w ∈ 𝒞(b_n, K_n)` admissible from the endpoint `R_h`, with
endpoint `src(w, R_h)` and weight `ω(h) ω(w)`. Evaluating the lifted transfer at the integer
point `[R_h]_Q` gives `ω(w) [w admissible from R_h] ρ_{k_{n+1}}(src(w, R_h))`, so both
`Z_{n+1}(t)` and `Z_n(t)` are sums over `h ∈ 𝓗_n(t)` of `ω(h)` times a function of
`R_h mod 3^Q`; grouping the histories by this residue gives the histogram.

## Main definitions

* `CollatzPosDens.centralIncrementDensity n`: the function `f_n : G_Q → ℝ`.

## Main results

* `CollatzPosDens.weightedCentralSum_succ_sub`:
  `Z_{n+1}(t) - Z_n(t) = ∑_y Hg_{n,Q}(y) f_n(y)` for `n ≥ j_e`.
* `CollatzPosDens.weightedCentralSum_succ_sub_sum_residueHistogram_mul`: pairing a
  function with the histogram is a sum over the central histories.

## Implementation notes

The lifted transfer `𝒯_{w,Q}` needs the bound `|w| + k_{n+1} ≤ Q`, which holds for every
`w ∈ 𝒞(b_n, K_n)` since `|w| ≤ h_{b_n}`; `f_n` is written with this bound as a condition, the
term being `0` when it fails, which never happens on `𝒞(b_n, K_n)`. The sum over
`𝒞(b_n, K_n)` is a `finsum` over this finite set. The identity holds for every integer `t`,
without oddness or positivity, and is stated so.

## References

* [Mazur, *Collatz positive density*], §16.5.
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

/-- The tuple `(w₀, …, w_{m-1}, w)` of length `M = m + 1` obtained by appending `w` to a tuple
`h = (w₀, …, w_{m-1})`. -/
private def tupleExtend {M m : ℕ} (e : M = m + 1) (h : Fin m → Word) (w : Word) :
    Fin M → Word :=
  fun k => Fin.snoc (α := fun _ => Word) h w (Fin.cast e k)

/-- The splitting of a tuple of length `M = m + 1` into its first `m` entries and its last
entry. -/
private def tupleSplit {M m : ℕ} (e : M = m + 1) (h : Fin M → Word) : (Fin m → Word) × Word :=
  (fun k => h (Fin.cast e.symm k.castSucc), h (Fin.cast e.symm (Fin.last m)))

private lemma tupleExtend_split {M m : ℕ} (e : M = m + 1) (h : Fin M → Word) :
    tupleExtend e (tupleSplit e h).1 (tupleSplit e h).2 = h := by
  subst e
  funext k
  cases k using Fin.lastCases with
  | last => simp [tupleExtend, tupleSplit]
  | cast j => simp [tupleExtend, tupleSplit]

private lemma tupleSplit_extend {M m : ℕ} (e : M = m + 1) (h : Fin m → Word) (w : Word) :
    tupleSplit e (tupleExtend e h w) = (h, w) := by
  subst e
  simp [tupleSplit, tupleExtend]

private lemma tupleExtend_castLE {M m : ℕ} (e : M = m + 1) (h : Fin m → Word) (w : Word)
    (hle : m ≤ M) (k : Fin m) : tupleExtend e h w (Fin.castLE hle k) = h k := by
  subst e
  simp [tupleExtend, Fin.snoc, Fin.castLE]

private lemma concatWord_tupleExtend {M m : ℕ} (e : M = m + 1) (h : Fin m → Word) (w : Word) :
    concatWord (tupleExtend e h w) = concatWord h ++ w := by
  subst e
  exact concatWord_snoc h w

/-- An entrywise condition on a tuple of length `M = m + 1` is the condition on its first `m`
entries together with the condition on its last entry. -/
private lemma forall_tupleExtend_iff {M m : ℕ} (e : M = m + 1) (h : Fin m → Word) (w : Word)
    (P : ℕ → Word → Prop) :
    (∀ k : Fin M, P k (tupleExtend e h w k)) ↔ (∀ k : Fin m, P k (h k)) ∧ P m w := by
  subst e
  simp [tupleExtend, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]

/-- The tuple `(w₀, …, w_{n-1}, w)` of generation `n + 1` obtained by appending `w` to a tuple
`h = (w₀, …, w_{n-1})` of generation `n`. -/
private abbrev historyExtend (h : Fin n → Word) (w : Word) : Fin (n + 1) → Word :=
  tupleExtend rfl h w

/-- The splitting of a tuple of generation `n + 1` into its first `n` entries and its last
entry. -/
private abbrev historySplit (h : Fin (n + 1) → Word) : (Fin n → Word) × Word :=
  tupleSplit rfl h

private lemma historyEndpoint_historyExtend (t : ℚ) (h : Fin n → Word) (w : Word) :
    historyEndpoint t (historyExtend h w) = src w (historyEndpoint t h) := by
  rw [historyEndpoint_eq_src, historyEndpoint_eq_src, concatWord_tupleExtend rfl h w,
    src_append]

/-- From generation `j_e` on, a central history of generation `n + 1` is a central history `h` of
generation `n` followed by a word of `𝒞(b_n, K_n)` admissible from the endpoint `R_h`. -/
private lemma historyExtend_mem_centralHistories_iff (hn : selEnd ≤ n) {t : ℚ}
    {h : Fin n → Word} {w : Word} :
    historyExtend h w ∈ centralHistories t (n + 1) ↔ h ∈ centralHistories t n ∧
      w ∈ centralFamily (scale n) (cap n) ∧ Admissible (historyEndpoint t h) w := by
  have hres : (fun k : Fin n => historyExtend h w (Fin.castLE (by omega) k)) = h :=
    funext fun k => tupleExtend_castLE _ h w _ k
  have hsel : selector (n + 1) (historyExtend h w) ↔ selector n h := by
    rw [← selector_restrict_iff (j := n) hn (by omega), hres]
  have hfam := forall_tupleExtend_iff rfl h w
    (fun k v => v ∈ centralFamily (scale k) (cap k))
  rw [mem_centralHistories, mem_selectedTuples, hfam, hsel,
    concatWord_tupleExtend rfl h w, admissible_append, mem_centralHistories,
    mem_selectedTuples, historyEndpoint_eq_src]
  exact ⟨fun ⟨⟨⟨a, b⟩, c⟩, d, e⟩ => ⟨⟨⟨a, c⟩, d⟩, b, e⟩,
    fun ⟨⟨⟨a, c⟩, d⟩, b, e⟩ => ⟨⟨⟨a, b⟩, c⟩, d, e⟩⟩

/-- The endpoint of a central history from an integer is an integer. -/
private lemma intCast_num_historyEndpoint {t : ℤ} {h : Fin n → Word}
    (hh : h ∈ centralHistories t n) :
    ((historyEndpoint t h).num : ℚ) = historyEndpoint t h := by
  refine Rat.coe_int_num_of_den_eq_one ?_
  rw [historyEndpoint_eq_src]
  exact hh.2.den_src_eq_one

/-- Pairing a function with the histogram groups the histories by endpoint residue. -/
theorem weightedCentralSum_succ_sub_sum_residueHistogram_mul (t : ℤ) (n q : ℕ)
    (φ : ResidueGroup q → ℝ) :
    ∑ y, residueHistogram t n q y * φ y =
      ∑ h ∈ (centralHistories_finite t n).toFinset,
        ((concatWord h).weight : ℝ) * φ ((historyEndpoint t h).num : ResidueGroup q) := by
  classical
  have key : ∀ y, residueHistogram t n q y =
      ∑ h ∈ (centralHistories_finite t n).toFinset with
        ((historyEndpoint t h).num : ResidueGroup q) = y, ((concatWord h).weight : ℝ) := by
    intro y
    rw [residueHistogram_eq_sum]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext h
    simp only [mem_filter, Set.Finite.mem_toFinset]
    refine and_congr_right fun hh =>
      ⟨?_, fun hy => ⟨_, intCast_num_historyEndpoint hh, hy⟩⟩
    rintro ⟨r, hr, rfl⟩
    rw [← intCast_num_historyEndpoint hh] at hr
    rw [show r = (historyEndpoint t h).num by exact_mod_cast hr]
  simp only [key, sum_mul]
  rw [← Finset.sum_fiberwise (centralHistories_finite t n).toFinset
    (fun h => ((historyEndpoint t h).num : ResidueGroup q))]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun h hh => ?_
  rw [(mem_filter.1 hh).2]

end

/-- **Increment identity.** For an integer `t` (in the source, odd and positive), `n ≥ j_e` and
`Q = h_{b_n} + k_{n+1}`: `Z_{n+1}(t) - Z_n(t) = ∑_{y ∈ G_Q} Hg_{n,Q}(y) f_n(y)`,
where `Hg_{n,Q}` is the residue histogram of `𝓗_n(t)`. -/
@[collatz_pos_dens "lem_Zn_increment_identity"]
theorem weightedCentralSum_succ_sub (t : ℤ) {n : ℕ} (hn : selEnd ≤ n) :
    weightedCentralSum (n + 1) t - weightedCentralSum n t =
      ∑ y, residueHistogram t n (hb (scale n) + level (n + 1)) y *
        centralIncrementDensity n y := by
  classical
  set Q := hb (scale n) + level (n + 1)
  have hC := centralFamily_finite (scale n) (cap n)
  set H := (centralHistories_finite (t : ℚ) n).toFinset
  have hf : ∀ h ∈ H, centralIncrementDensity n ((historyEndpoint t h).num : ResidueGroup Q) =
      (∑ w ∈ hC.toFinset, if Admissible (historyEndpoint t h) w then
          (w.weight : ℝ) * refDensity (level (n + 1))
            ((src w (historyEndpoint t h)).num : ResidueGroup (level (n + 1)))
        else 0) -
        refDensity (level n) ((historyEndpoint t h).num : ResidueGroup (level n)) := by
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
  · rewrite [weightedCentralSum_eq_sum]
    conv_rhs =>
      simp only [mul_sum, mul_ite, mul_zero]
      rw [← Finset.sum_product' (f := fun h w =>
        if Admissible (historyEndpoint t h) w then
          ((concatWord h).weight : ℝ) * ((w.weight : ℝ) * refDensity (level (n + 1))
            ((src w (historyEndpoint t h)).num : ResidueGroup (level (n + 1)))) else 0),
      ← Finset.sum_filter]
    refine Finset.sum_nbij' historySplit (fun p => historyExtend p.1 p.2) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      rw [Set.Finite.mem_toFinset, ← tupleExtend_split rfl h] at hh
      obtain ⟨h1, h2, h3⟩ := (historyExtend_mem_centralHistories_iff hn).1 hh
      simp only [mem_filter, mem_product, Set.Finite.mem_toFinset]
      exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨h, w⟩ hp
      simp only [mem_filter, mem_product, Set.Finite.mem_toFinset] at hp ⊢
      exact (historyExtend_mem_centralHistories_iff hn).2 ⟨hp.1.1, hp.1.2, hp.2⟩
    · intro h _
      exact tupleExtend_split _ h
    · rintro ⟨h, w⟩ _
      exact tupleSplit_extend _ h w
    · intro h _
      conv_lhs => rw [← tupleExtend_split rfl h]
      rw [concatWord_tupleExtend rfl, Word.weight_append, historyEndpoint_historyExtend]
      push_cast
      ring
  · rw [weightedCentralSum_eq_sum]

end CollatzPosDens
