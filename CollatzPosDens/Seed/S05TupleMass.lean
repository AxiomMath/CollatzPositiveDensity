/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.SelEnd
public import CollatzPosDens.Seed.S05ConcatWord
public import CollatzPosDens.Seed.S05OffsetCap
public import CollatzPosDens.Seed.S05PrefixResidue
public import CollatzPosDens.Seed.S05Selector
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Seed.S05FirstBlockMass
public import CollatzPosDens.Seed.S05LaterBlocksMass

/-!
# Mass of the selected tuples in the cylinder

Write `j_e = selEnd = 29`. For every `n ≥ j_e`, the selected central tuples `τ ∈ 𝔗_n` whose
concatenated word `ŵ(τ)` has length at least `8` and prefix residue `pr_8(ŵ(τ)) = [6275]_8` carry
total weight
$$\sum_{\substack{\tau\in\mathfrak T_n,\ |\hat w(\tau)|\ge8\\
  \mathrm{pr}_8(\hat w(\tau))=[6275]_8}} 2^{-A(\hat w(\tau))} >
  \Bigl(\frac{617014680840434}{2^{62}} - \frac1{20000000}\Bigr)
  \Bigl(\frac{199}{200} - 2^{-592}\Bigr).$$

Write `𝒞_i = 𝒞(b_i, K_i)` and `M_sel = 2^600` for the offset cap. For `n ≥ 1` the set `𝔗_n` is
the product of the sets `𝒮_0 = {v ∈ 𝒞_0 | off v ≤ 3/4}`, `𝒮_i = {v ∈ 𝒞_i | off v ≤ M_sel}` for
`0 < i < j_e`, and `𝒮_i = 𝒞_i` for `i ≥ j_e`. The first block `w_0` of a tuple is a prefix of
`ŵ(τ)` of length more than `ℓ_{b_0} = 16544 - ⌊3 · 16544 / 5⌋ = 6618`, so `|ŵ(τ)| ≥ 8` and
`pr_8(ŵ(τ)) = pr_8(w_0)`: the tuples summed are those of the product set in which `𝒮_0` is
replaced by `𝒮' = {v ∈ 𝒞_0 | |v| ≥ 8, off v ≤ 3/4, pr_8(v) = [6275]_8}`. Since the valuation
sum is additive under concatenation, the sum is `𝐩(𝒮') · ∏_{0 < i < n} 𝐩(𝒮_i)`, and the two
factors are bounded below by the first block mass and the later blocks mass.

## Main results

* `CollatzPosDens.tsum_setOf_forall_mem_eq_prod_geomMass`: the weight sum over a product set of
  tuples of words is the product of the geometric masses of the factors.
* `CollatzPosDens.two_inv_pow_lt_tsum_selectedTuples`: the lower bound on the mass of the
  selected tuples in the cylinder.

## Implementation notes

The sum is the unconditional sum in `ℝ≥0∞` of the weights `2⁻¹ ^ A(ŵ(τ))` over the subtype of
the tuples of `𝔗_n` satisfying the two conditions; in `ℝ≥0∞` every family is summable and the
sum over a product type is the iterated sum, so the product form needs no finiteness. The
residue `[6275]_8 ∈ G_8` is the dyadic reduction of the integer `6275`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- Appending a word of `S m` identifies the tuples `Fin m → Word` with entries `τ k ∈ S k`,
times `S m`, with the tuples `Fin (m + 1) → Word` with entries `τ k ∈ S k`. -/
private noncomputable def piSnocEquiv (m : ℕ) (S : ℕ → Set Word) :
    {τ : Fin m → Word | ∀ k : Fin m, τ k ∈ S k} × S m ≃
      {τ : Fin (m + 1) → Word | ∀ k : Fin (m + 1), τ k ∈ S k} where
  toFun p := ⟨Fin.snoc (p.1 : Fin m → Word) (p.2 : Word), by
    obtain ⟨⟨t, ht⟩, ⟨w, hw⟩⟩ := p
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hw
    · simpa using ht i⟩
  invFun t := ⟨⟨Fin.init (t : Fin (m + 1) → Word), fun k => by
      simpa [Fin.init] using t.2 (Fin.castSucc k)⟩,
    ⟨(t : Fin (m + 1) → Word) (Fin.last m), by simpa using t.2 (Fin.last m)⟩⟩
  left_inv p := by
    obtain ⟨⟨t, ht⟩, ⟨w, hw⟩⟩ := p
    simp
  right_inv t := by
    obtain ⟨t, ht⟩ := t
    simp

/-- For sets `S k` of words, the sum of `2^{-A(ŵ(τ))}` over the tuples
`τ : Fin m → Word` with `τ k ∈ S k` for all `k` is `∏_{k < m} 𝐩(S k)`. -/
theorem tsum_setOf_forall_mem_eq_prod_geomMass (m : ℕ) (S : ℕ → Set Word) :
    ∑' τ : {τ : Fin m → Word | ∀ k : Fin m, τ k ∈ S k},
        (2⁻¹ : ℝ≥0∞) ^ (concatWord (τ : Fin m → Word)).valSum =
      ∏ k ∈ Finset.range m, geomMass (S k) := by
  induction m with
  | zero =>
    rw [Finset.prod_range_zero, tsum_eq_single ⟨Fin.elim0, fun k => k.elim0⟩ fun b hb =>
      absurd (Subtype.ext (funext fun k => k.elim0)) hb]
    simp
  | succ m ih =>
    rw [← (piSnocEquiv m S).tsum_eq]
    simp only [piSnocEquiv, Equiv.coe_fn_mk, concatWord_snoc, Word.valSum_append, pow_add]
    rw [ENNReal.tsum_prod', Finset.prod_range_succ, ← ih, geomMass_def,
      ← ENNReal.tsum_mul_right]
    congr 1
    ext t
    rw [← ENNReal.tsum_mul_left]

/-- The selected factor `𝒮_i`: `{v ∈ 𝒞_0 | off v ≤ 3/4}` for `i = 0`,
`{v ∈ 𝒞_i | off v ≤ M_sel}` for `0 < i < j_e`, and `𝒞_i` for `i ≥ j_e`. -/
private noncomputable def selFactor (i : ℕ) : Set Word :=
  if i = 0 then {v ∈ centralFamily (scale i) (cap i) | off v ≤ 3 / 4}
  else if i < selEnd then {v ∈ centralFamily (scale i) (cap i) | off v ≤ offsetCap}
  else centralFamily (scale i) (cap i)

private theorem selFactor_zero :
    selFactor 0 = {v ∈ centralFamily (scale 0) (cap 0) | off v ≤ 3 / 4} := by
  rw [selFactor, ite_eq_left rfl]

private theorem selFactor_of_lt {i : ℕ} (h₁ : 0 < i) (h₂ : i < selEnd) :
    selFactor i = {v ∈ centralFamily (scale i) (cap i) | off v ≤ offsetCap} := by
  rw [selFactor, ite_eq_right (by omega), ite_eq_left h₂]

private theorem selFactor_of_le {i : ℕ} (h : selEnd ≤ i) :
    selFactor i = centralFamily (scale i) (cap i) := by
  rw [selEnd_eq] at h
  rw [selFactor, ite_eq_right (by omega), ite_eq_right (by rw [selEnd_eq]; omega)]

private theorem selFactor_subset (i : ℕ) : selFactor i ⊆ centralFamily (scale i) (cap i) := by
  unfold selFactor
  split_ifs
  · exact fun v hv => hv.1
  · exact fun v hv => hv.1
  · exact le_rfl

/-- For `n ≥ 1`, `𝔗_n` is the product set `∏_{0 ≤ i < n} 𝒮_i`. -/
private theorem selectedTuples_eq_setOf_forall_mem {n : ℕ} (hn : 0 < n) :
    selectedTuples n = {τ : Fin n → Word | ∀ k : Fin n, τ k ∈ selFactor k} := by
  ext τ
  rw [mem_selectedTuples, selector_iff]
  constructor
  · rintro ⟨hC, h0, hM⟩ k
    rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hk0
    · have hk : k = ⟨0, hn⟩ := Fin.ext hk0
      subst hk
      rw [selFactor_zero]
      exact ⟨hC ⟨0, hn⟩, h0 hn⟩
    rcases lt_or_ge (k : ℕ) selEnd with hks | hks
    · rw [selFactor_of_lt hk0 hks]
      exact ⟨hC k, hM k hk0 (lt_min k.2 hks)⟩
    · rw [selFactor_of_le hks]
      exact hC k
  · intro h
    replace h : ∀ k : Fin n, τ k ∈ selFactor k := h
    refine ⟨fun k => selFactor_subset _ (h k), fun h' => ?_, fun i hi hi' => ?_⟩
    · have := h ⟨0, h'⟩
      rw [show ((⟨0, h'⟩ : Fin n) : ℕ) = 0 from rfl, selFactor_zero] at this
      exact this.2
    · have := h ⟨i, lt_of_lt_of_le hi' (min_le_left _ _)⟩
      rw [show ((⟨i, lt_of_lt_of_le hi' (min_le_left _ _)⟩ : Fin n) : ℕ) = i from rfl,
        selFactor_of_lt hi (lt_of_lt_of_le hi' (min_le_right _ _))] at this
      exact this.2

/-- The first block of a nonempty tuple of words is a prefix of the concatenated word. -/
private theorem tupleMass_prefix_concatWord {N : ℕ} (t : Fin N → Word) (hN : 0 < N) :
    t ⟨0, hN⟩ <+: concatWord t := by
  cases N with
  | zero => omega
  | succ m =>
    rw [concatWord_succ']
    exact List.prefix_append _ _

/-- The prefix residue `pr_8` of a word is that of any prefix of length at least `8`. -/
private theorem tupleMass_prefixResidue_eq {v u : Word} (hvu : v <+: u) (hv : 8 ≤ v.length) :
    prefixResidue 8 u = prefixResidue 8 v := by
  obtain ⟨z, rfl⟩ := hvu
  rw [prefixResidue_def, prefixResidue_def, List.take_append_of_le_length hv]

/-- A word of `𝒞(b_0, K_0)` has length at least `8`, since `ℓ_{b_0} = 6618`. -/
private theorem tupleMass_eight_le_length {v : Word}
    (hv : v ∈ centralFamily (scale 0) (cap 0)) : 8 ≤ v.length := by
  have := lb_lt_length_of_mem_firstCrossing (centralFamily_subset_firstCrossing _ _ hv)
  have hlb : lb (scale 0) = 6618 := by rw [scale_zero, lb_eq]
  omega

/-- The selected factors in the cylinder: `selFactor` with the first factor replaced by
`𝒮' = {v ∈ 𝒞_0 | |v| ≥ 8, off v ≤ 3/4, pr_8(v) = [6275]_8}`. -/
private noncomputable def selFactorCyl (i : ℕ) : Set Word :=
  if i = 0 then {v ∈ centralFamily (scale 0) (cap 0) |
      8 ≤ v.length ∧ off v ≤ 3 / 4 ∧
        prefixResidue 8 v = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩}
  else selFactor i

private theorem selFactorCyl_zero :
    selFactorCyl 0 = {v ∈ centralFamily (scale 0) (cap 0) |
      8 ≤ v.length ∧ off v ≤ 3 / 4 ∧
        prefixResidue 8 v = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩} := by
  rw [selFactorCyl, ite_eq_left rfl]

private theorem selFactorCyl_of_ne {i : ℕ} (h : i ≠ 0) : selFactorCyl i = selFactor i := by
  rw [selFactorCyl, ite_eq_right h]

/-- For `n ≥ 1`, the tuples of `𝔗_n` with `|ŵ(τ)| ≥ 8` and `pr_8(ŵ(τ)) = [6275]_8` form the
product set `𝒮' × ∏_{0 < i < n} 𝒮_i`. -/
private theorem setOf_selectedTuples_prefixResidue_eq {n : ℕ} (hn : 0 < n) :
    {τ : Fin n → Word | τ ∈ selectedTuples n ∧ 8 ≤ (concatWord τ).length ∧
        prefixResidue 8 (concatWord τ) = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩} =
      {τ : Fin n → Word | ∀ k : Fin n, τ k ∈ selFactorCyl k} := by
  set k0 : Fin n := ⟨0, hn⟩ with hk0_def
  have hk0 : (k0 : ℕ) = 0 := rfl
  ext τ
  simp only [Set.mem_ofPred_eq]
  rw [selectedTuples_eq_setOf_forall_mem hn]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hS, hlen, hres⟩ k
    by_cases hk : (k : ℕ) = 0
    · have hk' : k = k0 := Fin.ext hk
      subst hk'
      rw [hk0, selFactorCyl_zero]
      have h0 := hS k0
      rw [hk0, selFactor_zero] at h0
      have h8 := tupleMass_eight_le_length h0.1
      refine ⟨h0.1, h8, h0.2, ?_⟩
      rw [← hres, tupleMass_prefixResidue_eq (tupleMass_prefix_concatWord τ hn) h8]
    · rw [selFactorCyl_of_ne hk]
      exact hS k
  · intro h
    have h0 := h k0
    rw [hk0, selFactorCyl_zero] at h0
    have hpre := tupleMass_prefix_concatWord τ hn
    refine ⟨fun k => ?_, h0.2.1.trans hpre.length_le, ?_⟩
    · by_cases hk : (k : ℕ) = 0
      · have hk' : k = k0 := Fin.ext hk
        subst hk'
        rw [hk0, selFactor_zero]
        exact ⟨h0.1, h0.2.2.1⟩
      · have := h k
        rwa [selFactorCyl_of_ne hk] at this
    · rw [tupleMass_prefixResidue_eq hpre h0.2.1]
      exact h0.2.2.2

/-- For every `n ≥ selEnd`, the sum of `2^{-A(ŵ(τ))}` over the tuples `τ ∈ 𝔗_n` with
`|ŵ(τ)| ≥ 8` and `pr_8(ŵ(τ)) = [6275]_8` exceeds
`(617014680840434/2^62 - 1/20000000)(199/200 - 2^{-592})`. -/
@[collatz_pos_dens "lem_s05_tuple_mass"]
theorem two_inv_pow_lt_tsum_selectedTuples (n : ℕ) (hn : selEnd ≤ n) :
    ((617014680840434 / 2 ^ 62 : ℝ≥0∞) - 20000000⁻¹) * (199 / 200 - 2⁻¹ ^ 592) <
      ∑' τ : {τ : Fin n → Word | τ ∈ selectedTuples n ∧
          8 ≤ (concatWord τ).length ∧
            prefixResidue 8 (concatWord τ) = dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩},
        (2⁻¹ : ℝ≥0∞) ^ (concatWord (τ : Fin n → Word)).valSum := by
  have hse : 0 < selEnd := by rw [selEnd_eq]; norm_num
  have hgn : 0 < n := lt_of_lt_of_le hse hn
  rw [setOf_selectedTuples_prefixResidue_eq hgn,
    tsum_setOf_forall_mem_eq_prod_geomMass n selFactorCyl, Finset.range_eq_Ico,
    Finset.prod_eq_prod_Ico_succ_bot hgn, selFactorCyl_zero]
  refine ENNReal.mul_lt_mul sub_lt_geomMass_setOf_mem_centralFamily_off_le ?_
  have hlater : ∏ i ∈ Finset.Ico (0 + 1) n, geomMass (selFactorCyl i) =
      (∏ i ∈ Finset.Ioo 0 selEnd,
          geomMass {v ∈ centralFamily (scale i) (cap i) | off v ≤ offsetCap}) *
        ∏ i ∈ Finset.Ico selEnd n, geomMass (centralFamily (scale i) (cap i)) := by
    rw [← Finset.prod_Ico_consecutive _ (show 0 + 1 ≤ selEnd by omega) hn,
      Finset.Ico_add_one_left_eq_Ioo]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i hi => ?_)
      (Finset.prod_congr rfl fun i hi => ?_)
    · rw [Finset.mem_Ioo] at hi
      rw [selFactorCyl_of_ne hi.1.ne', selFactor_of_lt hi.1 hi.2]
    · rw [Finset.mem_Ico] at hi
      rw [selFactorCyl_of_ne (by omega), selFactor_of_le hi.1]
  rw [hlater]
  exact sub_lt_prod_geomMass_laterBlocks n hn

end CollatzPosDens
