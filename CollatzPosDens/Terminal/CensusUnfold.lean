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
public import CollatzPosDens.Terminal.OvershootReduce
public import CollatzPosDens.Terminal.LastValuationShift
public import CollatzPosDens.Transfer.RefDensity

/-!
# Unfolding the marked terminal mass over the counted pairs

Let `k = k_n` be the residue level `CollatzPosDens.level n`, `ρ_k` the reference density
`CollatzPosDens.refDensity k`, `Θ_{n,X}(M)` the marked terminal mass `CollatzPosDens.markedMass`
and `Υ_{n,X}(M)` the unweighted terminal mass `CollatzPosDens.unweightedMass`, whose counted
pairs `(h, w)` form `CollatzPosDens.unweightedMassPairs`. Writing `R_h` for the endpoint of the
history `h` and `ω` for the weight of a word, the marked terminal mass is bounded by a sum over
the counted pairs:
$$\Theta_{n,X}(M) \le \sum_{(h,w)} \omega(h)\omega(w) \sum_{j \ge 0} 4^{-j}
  \rho_k\bigl((4^j \mathrm{src}(w, R_h) + (4^j - 1)/3) \bmod 3^k\bigr).$$
Every word `w` of the inner sum of `Θ_{n,X}(M)` arises, by the overshoot reduction, from a
word `w°` of `Υ_{n,X}(M)` by raising its last letter by `2j`; then
`src(w, R_h) = 4^j src(w°, R_h) + (4^j - 1)/3` and `ω(w) = 4^{-j} ω(w°)`. The assignment
`w ↦ (w°, j)` is injective, and all terms are nonnegative.

## Main results

* `CollatzPosDens.markedMass_le_tsum_unweightedMassPairs`: the bound above.
* `CollatzPosDens.summable_inv_four_pow_mul_of_le`: a nonnegative bounded sequence damped by
  `4^{-j}` is summable.

## Implementation notes

The sum over `j ≥ 0` is a `tsum`; it converges since `ρ_k` is bounded on the finite group
`ResidueGroup k`. As in `CollatzPosDens.markedMass`, the residue modulo `3^k` of the rational
`4^j src(w, R_h) + (4^j - 1)/3` is that of its numerator. The bound needs no hypothesis on `M`
or `X`, so it is stated for every rational `M` and real `X`.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

/-- The `j`-th summand `4^{-j} ρ_k((4^j x + (4^j - 1)/3) mod 3^k)` of the census bound. -/
private noncomputable def censusUnfoldTerm (k : ℕ) (x : ℚ) (j : ℕ) : ℝ :=
  ((4 : ℝ) ^ j)⁻¹ * refDensity k ((4 ^ j * x + (4 ^ j - 1) / 3 : ℚ).num : ResidueGroup k)

/-- A nonnegative bounded sequence damped by `4^{-j}` is summable. -/
theorem summable_inv_four_pow_mul_of_le {f : ℕ → ℝ} {B : ℝ} (hf0 : ∀ j, 0 ≤ f j)
    (hfB : ∀ j, f j ≤ B) : Summable fun j => ((4 : ℝ) ^ j)⁻¹ * f j :=
  Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (hf0 j))
    (fun j => by rw [← inv_pow]; exact mul_le_mul_of_nonneg_left (hfB j) (by positivity))
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 4⁻¹) (by norm_num)).mul_right B)

/-- The summands of the census bound are nonnegative. -/
private lemma censusUnfoldTerm_nonneg (k : ℕ) (x : ℚ) (j : ℕ) :
    0 ≤ censusUnfoldTerm k x j :=
  mul_nonneg (by positivity) (refDensity_nonneg _ _)

/-- The series of the census bound converges, since `ρ_k` is bounded on `G_k`. -/
private lemma summable_censusUnfoldTerm (k : ℕ) (x : ℚ) :
    Summable (censusUnfoldTerm k x) :=
  summable_inv_four_pow_mul_of_le (fun _ => refDensity_nonneg _ _)
    fun _ => Finset.single_le_sum (fun y _ => refDensity_nonneg k y) (Finset.mem_univ _)

/-- The word obtained from `q.1` by raising its last letter by `2 q.2`. -/
private def censusUnfoldRaise (q : Word × ℕ) : Word :=
  q.1.dropLast ++ [shiftLastLetter (q.1.getLast?.getD 1) q.2]

/-- Raising the last letter of `v ++ [a]` by `2j` gives `v ++ [a + 2j]`. -/
private lemma censusUnfoldRaise_concat (v : Word) (a : ℕ+) (j : ℕ) :
    censusUnfoldRaise (v ++ [a], j) = v ++ [shiftLastLetter a j] := by
  simp [censusUnfoldRaise]

/-- Every word of the inner sum of `Θ_{n,X}(M)` is a raised word of `Υ_{n,X}(M)`. -/
private lemma exists_censusUnfoldRaise {n : ℕ} {X : ℝ} {M : ℚ} {h : Fin n → Word}
    {w : Word} (hw : w ∈ markedMassWords n X M h) :
    ∃ (v : Word) (a : ℕ+) (j : ℕ),
      v ++ [a] ∈ unweightedMassWords n X M h ∧ w = v ++ [shiftLastLetter a j] := by
  obtain ⟨hfc, hlen, hadm⟩ := hw
  obtain ⟨v, a', rfl⟩ :=
    (List.eq_nil_or_concat' w).resolve_left (ne_nil_of_mem_firstCrossing hfc)
  obtain ⟨j, hj, hfc', hadm'⟩ := exists_overshoot_reduce hfc hadm
  set a : ℕ+ := ⟨a' - 2 * j, Nat.sub_pos_of_lt hj⟩
  have ha' : (a : ℕ) + 2 * j = a' := Nat.sub_add_cancel hj.le
  refine ⟨v, a, j, ⟨hfc', ?_, hadm'⟩, ?_⟩
  · have hl : (v ++ [a]).length = (v ++ [a']).length := by simp
    unfold LengthOk
    rw [hl]
    exact hlen
  · congr 2
    exact PNat.eq (by rw [coe_shiftLastLetter, ha'])

/-- Raising the last letter by `2j` multiplies the weight by `4^{-j}`. -/
private lemma weight_shiftLastLetter (v : Word) (a : ℕ+) (j : ℕ) :
    ((v ++ [shiftLastLetter a j]).weight : ℝ) =
      ((4 : ℝ) ^ j)⁻¹ * ((v ++ [a]).weight : ℝ) := by
  simp only [Word.weight_append, Word.weight_singleton, coe_shiftLastLetter]
  push_cast
  rw [pow_add, pow_mul]
  field_simp
  norm_num

/-- For one history `h`, the inner sum of `Θ_{n,X}(M)` is at most the inner census sum over
the words of `Υ_{n,X}(M)`. -/
private lemma sum_markedWords_le_sum_unweightedMassWords {n : ℕ} {X : ℝ} {M : ℚ}
    (h : Fin n → Word) (k : ℕ) (R : ℚ) :
    ∑ w ∈ (markedMassWords_finite n X M h).toFinset,
        (w.weight : ℝ) * refDensity k ((src w R).num : ResidueGroup k) ≤
      ∑ w ∈ (unweightedMassWords_finite n X M h).toFinset,
        (w.weight : ℝ) * ∑' j : ℕ, censusUnfoldTerm k (src w R) j := by
  set S := (markedMassWords_finite n X M h).toFinset
  set T := (unweightedMassWords_finite n X M h).toFinset
  have hex : ∀ w ∈ S, ∃ q : Word × ℕ,
      q.1 ∈ T ∧ q.1 ≠ [] ∧ censusUnfoldRaise q = w := by
    intro w hw
    obtain ⟨v, a, j, hva, rfl⟩ := exists_censusUnfoldRaise (by simpa [S] using hw)
    exact ⟨(v ++ [a], j), by simpa [T] using hva, by simp, censusUnfoldRaise_concat v a j⟩
  choose! φ hφT hφne hφ using hex
  let g : Word × ℕ → ℝ := fun q => (q.1.weight : ℝ) * censusUnfoldTerm k (src q.1 R) q.2
  have hg : ∀ w ∈ S, (w.weight : ℝ) * refDensity k ((src w R).num : ResidueGroup k) =
      g (φ w) := by
    intro w hw
    obtain ⟨v, a, hva⟩ := (List.eq_nil_or_concat' (φ w).1).resolve_left (hφne w hw)
    have e := hφ w hw
    rcases hq : φ w with ⟨q, j⟩
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
    _ = ∑ w ∈ T, ∑ j ∈ (S.image φ).image Prod.snd, g (w, j) := Finset.sum_product ..
    _ ≤ ∑ w ∈ T, (w.weight : ℝ) * ∑' j : ℕ, censusUnfoldTerm k (src w R) j := by
          refine Finset.sum_le_sum fun w _ => ?_
          simp only [g, ← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            ((summable_censusUnfoldTerm k _).sum_le_tsum _ fun j _ =>
              censusUnfoldTerm_nonneg ..)
            (by exact_mod_cast (Word.weight_pos _).le)

/-- **Census unfolding.** The marked terminal mass is at most
`∑_{(h,w)} ω(h) ω(w) ∑_{j ≥ 0} 4^{-j} ρ_k((4^j src(w, R_h) + (4^j - 1)/3) mod 3^k)`,
the outer sum over the counted pairs of `Υ_{n,X}(M)` and `k = k_n`. -/
@[collatz_pos_dens "lem_s06_census_unfold"]
theorem markedMass_le_tsum_unweightedMassPairs (n : ℕ) (X : ℝ) (M : ℚ) :
    markedMass n X M ≤ ∑ᶠ p ∈ unweightedMassPairs n X M,
      ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        ∑' j : ℕ, ((4 : ℝ) ^ j)⁻¹ * refDensity (level n)
          ((4 ^ j * src p.2 (historyEndpoint M p.1) + (4 ^ j - 1) / 3 : ℚ).num :
            ResidueGroup (level n)) := by
  classical
  set k := level n
  have hrhs : (∑ᶠ p ∈ unweightedMassPairs n X M,
      ((concatWord p.1).weight : ℝ) * (p.2.weight : ℝ) *
        ∑' j : ℕ, ((4 : ℝ) ^ j)⁻¹ * refDensity k
          ((4 ^ j * src p.2 (historyEndpoint M p.1) + (4 ^ j - 1) / 3 : ℚ).num :
            ResidueGroup k)) =
      ∑ h ∈ (centralHistories_finite M n).toFinset,
        ((concatWord h).weight : ℝ) *
          ∑ w ∈ (unweightedMassWords_finite n X M h).toFinset, (w.weight : ℝ) *
            ∑' j : ℕ, censusUnfoldTerm k (src w (historyEndpoint M h)) j := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (unweightedMassPairs_finite ..)]
    simp_rw [Finset.mul_sum, censusUnfoldTerm, mul_assoc]
    have hmem : ∀ p : (Fin n → Word) × Word,
        p ∈ (unweightedMassPairs_finite n X M).toFinset ↔
          p.1 ∈ (centralHistories_finite M n).toFinset ∧
            p.2 ∈ (unweightedMassWords_finite n X M p.1).toFinset := fun p => by
      simp only [Set.Finite.mem_toFinset]
      rfl
    exact Finset.sum_finset_product' _ _
      (fun h => (unweightedMassWords_finite n X M h).toFinset) hmem (f := fun h w =>
      ((concatWord h).weight : ℝ) * ((w.weight : ℝ) * ∑' j : ℕ, ((4 : ℝ) ^ j)⁻¹ *
        refDensity k ((4 ^ j * src w (historyEndpoint M h) + (4 ^ j - 1) / 3 : ℚ).num :
          ResidueGroup k)))
  rw [hrhs, markedMass_eq_sum]
  exact Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
    (sum_markedWords_le_sum_unweightedMassWords h k _) (by exact_mod_cast (Word.weight_pos _).le)

end CollatzPosDens
