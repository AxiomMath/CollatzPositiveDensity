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
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.SurvivalProduct
public import CollatzPosDens.Seed.ConcatWord
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Seed.SelectedRatio

/-!
# Mass of the selected tuples

For every `n ≥ 5`, the selected central tuples `𝔗_n` carry total weight
$$\sum_{t \in \mathfrak T_n} 2^{-A(\hat w(t))} > 2^{-23}.$$

For `n ≥ 5` a tuple of `𝔗_{n+1}` is a tuple of `𝔗_n` followed by an arbitrary word of
`𝒞(b_n, K_n)`, and the valuation sum is additive under concatenation, so the sum over `𝔗_{n+1}`
is the sum over `𝔗_n` times `𝐩(𝒞(b_n, K_n))`. Hence the sum over `𝔗_n` equals the sum over
`𝔗_5` times `∏_{5 ≤ j < n} 𝐩(𝒞(b_j, K_j))`, which exceeds `½ ∏_{j<n} 𝐩(𝒞(b_j, K_j))` by the
selector ratio bound, and this exceeds `½ · 2^{-22}` by the survival product bound.

## Main results

* `CollatzPosDens.two_inv_pow_lt_tsum_selectedTuples`: the lower bound `2^{-23}`.

## Implementation notes

The sum is the unconditional sum in `ℝ≥0∞` of the weights `2⁻¹ ^ A(ŵ(t))` over the subtype
`𝔗_n`, as in the selector ratio bound. The factorisation needs no finiteness: in `ℝ≥0∞` every
family is summable, and the sum over a product type is the iterated sum.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For `n ≥ 5`, appending a word of `𝒞(b_n, K_n)` identifies `𝔗_n × 𝒞(b_n, K_n)` with
`𝔗_{n+1}`. -/
private noncomputable def snocEquiv (n : ℕ) (hn : 5 ≤ n) :
    selectedTuples n × centralFamily (scale n) (cap n) ≃ selectedTuples (n + 1) where
  toFun p := ⟨Fin.snoc (p.1 : Fin n → Word) (p.2 : Word), by
    obtain ⟨⟨t, ht⟩, ⟨w, hw⟩⟩ := p
    refine ⟨fun j => ?_, fun _ => ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hw
      · simpa using ht.1 i
    · convert ht.2 hn using 1 <;> exact Fin.snoc_castSucc (i := ⟨_, by omega⟩) ..⟩
  invFun t := ⟨⟨Fin.init (t : Fin (n + 1) → Word), selectedTuples_restrict (Nat.le_succ n) t.2⟩,
    ⟨(t : Fin (n + 1) → Word) (Fin.last n), by simpa using t.2.1 (Fin.last n)⟩⟩
  left_inv p := by
    obtain ⟨⟨t, ht⟩, ⟨w, hw⟩⟩ := p
    simp
  right_inv t := by
    obtain ⟨t, ht⟩ := t
    simp

/-- For `n ≥ 5`, the sum of `2^{-A(ŵ(t))}` over `𝔗_{n+1}` is the sum over `𝔗_n` times the
mass `𝐩(𝒞(b_n, K_n))`. -/
private theorem tsum_selectedTuples_succ (n : ℕ) (hn : 5 ≤ n) :
    ∑' t : selectedTuples (n + 1), (2⁻¹ : ℝ≥0∞) ^ (concatWord (t : Fin (n + 1) → Word)).valSum =
      (∑' t : selectedTuples n, (2⁻¹ : ℝ≥0∞) ^ (concatWord (t : Fin n → Word)).valSum) *
        geomMass (centralFamily (scale n) (cap n)) := by
  rw [← (snocEquiv n hn).tsum_eq]
  simp only [snocEquiv, Equiv.coe_fn_mk, concatWord_snoc, Word.valSum_append, pow_add]
  rw [ENNReal.tsum_prod', geomMass_def, ← ENNReal.tsum_mul_right]
  congr 1
  ext t
  rw [← ENNReal.tsum_mul_left]

/-- For `n ≥ 5`, the sum over `𝔗_n` is the sum over `𝔗_5` times `∏_{5 ≤ j < n} 𝐩(𝒞(b_j, K_j))`. -/
private theorem tsum_selectedTuples_eq_mul_prod (n : ℕ) (hn : 5 ≤ n) :
    ∑' t : selectedTuples n, (2⁻¹ : ℝ≥0∞) ^ (concatWord (t : Fin n → Word)).valSum =
      (∑' t : selectedTuples 5, (2⁻¹ : ℝ≥0∞) ^ (concatWord (t : Fin 5 → Word)).valSum) *
        ∏ j ∈ Finset.Ico 5 n, geomMass (centralFamily (scale j) (cap j)) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [tsum_selectedTuples_succ n hn, ih, Finset.prod_Ico_succ_top hn, mul_assoc]

/-- **Mass of the selected tuples**. For every `n ≥ 5`, `∑_{t ∈ 𝔗_n} 2^{-A(ŵ(t))} > 2^{-23}`. -/
@[collatz_pos_dens "lem_s05_tuple_mass"]
theorem two_inv_pow_lt_tsum_selectedTuples (n : ℕ) (hn : 5 ≤ n) :
    (2⁻¹ : ℝ≥0∞) ^ 23 <
      ∑' t : selectedTuples n, (2⁻¹ : ℝ≥0∞) ^ (concatWord (t : Fin n → Word)).valSum := by
  set p : ℕ → ℝ≥0∞ := fun j => geomMass (centralFamily (scale j) (cap j))
  have hQ0 : ∏ j ∈ Finset.Ico 5 n, p j ≠ 0 := by
    have h := two_inv_pow_lt_prod_geomMass_centralFamily n
    rw [← Finset.prod_range_mul_prod_Ico _ hn] at h
    intro h0
    simp [p, h0] at h
  have hQT : ∏ j ∈ Finset.Ico 5 n, p j ≠ ⊤ :=
    ENNReal.prod_ne_top fun j _ =>
      ne_top_of_le_ne_top ENNReal.one_ne_top (geomMass_centralFamily_le_one _ _)
  rw [tsum_selectedTuples_eq_mul_prod n hn]
  calc (2⁻¹ : ℝ≥0∞) ^ 23 = 2⁻¹ * 2⁻¹ ^ 22 := by ring
    _ < 2⁻¹ * ∏ j ∈ Finset.range n, p j :=
        ENNReal.mul_lt_mul_right (by simp) (by simp)
          (two_inv_pow_lt_prod_geomMass_centralFamily n)
    _ = (2⁻¹ * ∏ j ∈ Finset.range 5, p j) * ∏ j ∈ Finset.Ico 5 n, p j := by
        rw [← Finset.prod_range_mul_prod_Ico _ hn, mul_assoc]
    _ < _ := (ENNReal.mul_lt_mul_iff_left hQ0 hQT).2
        half_mul_prod_geomMass_lt_tsum_selectedTuples_five

end CollatzPosDens
