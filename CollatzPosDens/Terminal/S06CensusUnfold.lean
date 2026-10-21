/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.MarkedMass
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.S06OvershootReduce
public import CollatzPosDens.Terminal.LastValuationShift
public import CollatzPosDens.Transfer.RefDensity

/-!
# Unfolding the marked terminal mass over the counted pairs

Write `k = k_j`. The marked terminal mass is bounded by a sum over the counted pairs `(h, w)` of
the unweighted terminal mass `Υ_{j,X}(t)`:
$$\Theta_{j,X}(t) \le \sum_{(h,w)} \omega(h)\omega(w) \sum_{i \ge 0} 4^{-i}
  \rho_k\bigl((4^i \mathrm{src}(w, R_h) + (4^i - 1)/3) \bmod 3^k\bigr).$$
Every word `w` of the inner sum of `Θ_{j,X}(t)` arises, by the overshoot reduction, from a
word `w°` of `Υ_{j,X}(t)` by raising its last letter by `2i`; then
`src(w, R_h) = 4^i src(w°, R_h) + (4^i - 1)/3` and `ω(w) = 4^{-i} ω(w°)`. The assignment
`w ↦ (w°, i)` is injective, and all terms are nonnegative.

## Main results

* `CollatzPosDens.markedMass_le_tsum_unweightedMassPairs`: the bound above.
* `CollatzPosDens.summable_inv_four_pow_mul_of_le`: a nonnegative bounded sequence damped by
  `4^{-i}` is summable.

## Implementation notes

The sum over `i ≥ 0` is a `tsum`; it converges since `ρ_k` is bounded on the finite group
`G_k`. As in `CollatzPosDens.markedMass`, the residue modulo `3^k` of the rational
`4^i src(w, R_h) + (4^i - 1)/3` is that of its numerator. The source takes `t` odd and
positive and `X > 0`; these hypotheses are not used, so the bound is stated for every rational
`t` and real `X`.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

/-- The `i`-th summand `4^{-i} ρ_k((4^i x + (4^i - 1)/3) mod 3^k)` of the census bound. -/
private noncomputable def censusUnfoldTerm (k : ℕ) (x : ℚ) (i : ℕ) : ℝ :=
  ((4 : ℝ) ^ i)⁻¹ * refDensity k ((4 ^ i * x + (4 ^ i - 1) / 3 : ℚ).num : ResidueGroup k)

/-- A nonnegative bounded sequence damped by `4^{-i}` is summable. -/
theorem summable_inv_four_pow_mul_of_le {f : ℕ → ℝ} {B : ℝ} (hf0 : ∀ i, 0 ≤ f i)
    (hfB : ∀ i, f i ≤ B) : Summable fun i => ((4 : ℝ) ^ i)⁻¹ * f i :=
  Summable.of_nonneg_of_le (fun i => mul_nonneg (by positivity) (hf0 i))
    (fun i => by rw [← inv_pow]; exact mul_le_mul_of_nonneg_left (hfB i) (by positivity))
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 4⁻¹) (by norm_num)).mul_right B)

/-- The summands of the census bound are nonnegative. -/
private lemma censusUnfoldTerm_nonneg (k : ℕ) (x : ℚ) (i : ℕ) :
    0 ≤ censusUnfoldTerm k x i :=
  mul_nonneg (by positivity) (refDensity_nonneg _ _)

/-- The series of the census bound converges, since `ρ_k` is bounded on `G_k`. -/
private lemma summable_censusUnfoldTerm (k : ℕ) (x : ℚ) :
    Summable (censusUnfoldTerm k x) :=
  summable_inv_four_pow_mul_of_le (fun _ => refDensity_nonneg _ _)
    fun _ => Finset.single_le_sum (fun y _ => refDensity_nonneg k y) (Finset.mem_univ _)

/-- The word obtained from `q.1` by raising its last letter by `2 q.2`. -/
private def censusUnfoldRaise (q : Word × ℕ) : Word :=
  q.1.dropLast ++ [shiftLastLetter (q.1.getLast?.getD 1) q.2]

/-- Raising the last letter of `v ++ [a]` by `2i` gives `v ++ [a + 2i]`. -/
private lemma censusUnfoldRaise_concat (v : Word) (a : ℕ+) (i : ℕ) :
    censusUnfoldRaise (v ++ [a], i) = v ++ [shiftLastLetter a i] := by
  simp [censusUnfoldRaise]

/-- Every word of the inner sum of `Θ_{j,X}(t)` is a raised word of `Υ_{j,X}(t)`. -/
private lemma exists_censusUnfoldRaise {j : ℕ} {X : ℝ} {t : ℚ} {h : Fin j → Word}
    {w : Word} (hw : w ∈ markedMassWords j X t h) :
    ∃ (v : Word) (a : ℕ+) (i : ℕ),
      v ++ [a] ∈ unweightedMassWords j X t h ∧ w = v ++ [shiftLastLetter a i] := by
  obtain ⟨hfc, hlen, hadm⟩ := hw
  obtain ⟨v, a', rfl⟩ :=
    (List.eq_nil_or_concat' w).resolve_left (ne_nil_of_mem_firstCrossing hfc)
  obtain ⟨i, hi, hfc', hadm'⟩ := exists_overshoot_reduce hfc hadm
  set a : ℕ+ := ⟨a' - 2 * i, Nat.sub_pos_of_lt hi⟩
  have ha' : (a : ℕ) + 2 * i = a' := Nat.sub_add_cancel hi.le
  refine ⟨v, a, i, ⟨hfc', ?_, hadm'⟩, ?_⟩
  · have hl : (v ++ [a]).length = (v ++ [a']).length := by simp
    unfold LengthOk
    rw [hl]
    exact hlen
  · congr 2
    exact PNat.eq (by rw [coe_shiftLastLetter, ha'])

/-- Raising the last letter by `2i` multiplies the weight by `4^{-i}`. -/
private lemma weight_shiftLastLetter (v : Word) (a : ℕ+) (i : ℕ) :
    ((v ++ [shiftLastLetter a i]).weight : ℝ) =
      ((4 : ℝ) ^ i)⁻¹ * ((v ++ [a]).weight : ℝ) := by
  simp only [Word.weight_append, Word.weight_singleton, coe_shiftLastLetter]
  push_cast
  rw [pow_add, pow_mul]
  field_simp
  norm_num

/-- For one history `h`, the inner sum of `Θ_{j,X}(t)` is at most the inner census sum over
the words of `Υ_{j,X}(t)`. -/
private lemma sum_markedWords_le_sum_unweightedMassWords {j : ℕ} {X : ℝ} {t : ℚ}
    (h : Fin j → Word) (k : ℕ) (R : ℚ) :
    ∑ w ∈ (markedMassWords_finite j X t h).toFinset,
        (w.weight : ℝ) * refDensity k ((src w R).num : ResidueGroup k) ≤
      ∑ w ∈ (unweightedMassWords_finite j X t h).toFinset,
        (w.weight : ℝ) * ∑' i : ℕ, censusUnfoldTerm k (src w R) i := by
  set S := (markedMassWords_finite j X t h).toFinset
  set T := (unweightedMassWords_finite j X t h).toFinset
  have hex : ∀ w ∈ S, ∃ q : Word × ℕ,
      q.1 ∈ T ∧ q.1 ≠ [] ∧ censusUnfoldRaise q = w := by
    intro w hw
    obtain ⟨v, a, i, hva, rfl⟩ := exists_censusUnfoldRaise (by simpa [S] using hw)
    exact ⟨(v ++ [a], i), by simpa [T] using hva, by simp, censusUnfoldRaise_concat v a i⟩
  choose! φ hφT hφne hφ using hex
  let g : Word × ℕ → ℝ := fun q => (q.1.weight : ℝ) * censusUnfoldTerm k (src q.1 R) q.2
  have hg : ∀ w ∈ S, (w.weight : ℝ) * refDensity k ((src w R).num : ResidueGroup k) =
      g (φ w) := by
    intro w hw
    obtain ⟨v, a, hva⟩ := (List.eq_nil_or_concat' (φ w).1).resolve_left (hφne w hw)
    have e := hφ w hw
    rcases hq : φ w with ⟨q, i⟩
    rw [hq] at e hva
    subst hva
    rw [censusUnfoldRaise_concat] at e
    subst e
    simp only [g, censusUnfoldTerm, weight_shiftLastLetter, src_shiftLastLetter]
    ring
  calc ∑ w ∈ S, (w.weight : ℝ) * refDensity k ((src w R).num : ResidueGroup k)
      = ∑ w ∈ S, g (φ w) := Finset.sum_congr rfl hg
    _ = ∑ q ∈ S.image φ, g q := (Finset.sum_image fun x hx y hy hxy => by
          rw [← hφ x hx, ← hφ y hy, hxy]).symm
    _ ≤ ∑ q ∈ T ×ˢ (S.image φ).image Prod.snd, g q := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q _ _ =>
            mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) (censusUnfoldTerm_nonneg _ _ _)
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hq
          exact Finset.mem_product.2 ⟨hφT w hw, Finset.mem_image_of_mem _ hq⟩
    _ = ∑ w ∈ T, ∑ i ∈ (S.image φ).image Prod.snd, g (w, i) := Finset.sum_product ..
    _ ≤ ∑ w ∈ T, (w.weight : ℝ) * ∑' i : ℕ, censusUnfoldTerm k (src w R) i := by
          refine Finset.sum_le_sum fun w _ => ?_
          simp only [g, ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            ((summable_censusUnfoldTerm k _).sum_le_tsum _ fun i _ =>
              censusUnfoldTerm_nonneg ..)
            (by exact_mod_cast (Word.weight_pos _).le)

/-- **Census unfolding.** The marked terminal mass is at most
`∑_{(h,w)} ω(h) ω(w) ∑_{i ≥ 0} 4^{-i} ρ_k((4^i src(w, R_h) + (4^i - 1)/3) mod 3^k)`,
the outer sum over the counted pairs of `Υ_{j,X}(t)` and `k = k_j`. -/
@[collatz_pos_dens "lem_s06_census_unfold"]
theorem markedMass_le_tsum_unweightedMassPairs (j : ℕ) (X : ℝ) (t : ℚ) :
    markedMass j X t ≤ ∑ᶠ p ∈ unweightedMassPairs j X t,
      ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        ∑' i : ℕ, ((4 : ℝ) ^ i)⁻¹ * refDensity (level j)
          ((4 ^ i * src p.2 (historyEndpoint t p.1) + (4 ^ i - 1) / 3 : ℚ).num :
            ResidueGroup (level j)) := by
  classical
  set k := level j
  have hrhs : (∑ᶠ p ∈ unweightedMassPairs j X t,
      ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        ∑' i : ℕ, ((4 : ℝ) ^ i)⁻¹ * refDensity k
          ((4 ^ i * src p.2 (historyEndpoint t p.1) + (4 ^ i - 1) / 3 : ℚ).num :
            ResidueGroup k)) =
      ∑ h ∈ (centralHistories_finite t j).toFinset,
        ((concatWord h).weight : ℝ) *
          ∑ w ∈ (unweightedMassWords_finite j X t h).toFinset, (w.weight : ℝ) *
            ∑' i : ℕ, censusUnfoldTerm k (src w (historyEndpoint t h)) i := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)]
    simp_rw [Finset.mul_sum, censusUnfoldTerm, mul_assoc]
    have hmem : ∀ p : (Fin j → Word) × Word,
        p ∈ (unweightedMassPairs_finite j X t).toFinset ↔
          p.1 ∈ (centralHistories_finite t j).toFinset ∧
            p.2 ∈ (unweightedMassWords_finite j X t p.1).toFinset := fun p => by
      simp only [Set.Finite.mem_toFinset]
      rfl
    exact Finset.sum_finset_product' _ _
      (fun h => (unweightedMassWords_finite j X t h).toFinset) hmem (f := fun h w =>
      ((concatWord h).weight : ℝ) * ((w.weight : ℝ) * ∑' i : ℕ, ((4 : ℝ) ^ i)⁻¹ *
        refDensity k ((4 ^ i * src w (historyEndpoint t h) + (4 ^ i - 1) / 3 : ℚ).num :
          ResidueGroup k)))
  rw [hrhs, markedMass_eq_sum]
  exact Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
    (sum_markedWords_le_sum_unweightedMassWords h k _) (by exact_mod_cast (Word.weight_pos _).le)

end CollatzPosDens
