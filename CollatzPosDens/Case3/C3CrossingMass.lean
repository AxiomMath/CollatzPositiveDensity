/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CrossingTransfer
public import CollatzPosDens.Renewal.RnHoldMass
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# Mass of the first raw crossing sets

For `ω ∈ ℕ` and integers `c, o, r` with `c ≥ 2`, `1 ≤ o ≤ c` and `r ≥ 1`, the first raw crossing
set `𝒞_ω(c, o, r)` carries total weight
`∑_{π ∈ 𝒞_ω(c, o, r)} bw^⊗(π) = ϖ(c) 𝖱(r - 1, ω + o - c)`.

The raw word map identifies `𝒞_ω(c, o, r)` with the words `w (c) u`, where `w ∈ ℤ^{r-1}` has
letters at least `2` and letter sum `ω + o - c` and `u ∈ 𝒮_c` is a suffix word of `c`, and the
weight factors along it (`tsum_c3CrossingSet_mul_eq`, applied with `Ψ ≡ 1`). The sum over `w` of
`∏ ϖ(wᵢ)` is `𝖱(r - 1, ω + o - c)` by definition. The sum over `u ∈ 𝒮_c` of `∏ ϖ(uᵢ)` is `1`:
for `c ∈ {4, 5}` it is the weight of the empty word, and otherwise `𝒮_c` is the disjoint union of
the hold words `𝒞_{j,l}`, `(j, l) ∈ 𝒫` (a hold word determines its length and its letter sum), so
the sum is `∑_{(j,l) ∈ 𝒫} η(j, l) = 1`.

## Main results

* `CollatzPosDens.tsum_ofReal_prod_varpi_rawWords`: the words `w ∈ ℤ^k` with letters at least `2`
  and letter sum `t` have total weight `𝖱(k, t)`.
* `CollatzPosDens.tsum_ofReal_prod_varpi_c3SuffixWords`: the suffix words of `c` have total
  weight `1`.
* `CollatzPosDens.hasSum_trListWeight_c3CrossingSet`: the series
  `∑_{π ∈ 𝒞_ω(c, o, r)} bw^⊗(π)` converges (unconditionally) to `ϖ(c) 𝖱(r - 1, ω + o - c)`.
* `CollatzPosDens.tsum_trListWeight_c3CrossingSet`: the same identity for `tsum`.

## Implementation notes

The sum over `𝒞_ω(c, o, r)` is stated as a `HasSum` over the subtype `c3CrossingSet ω c o r`,
which records convergence as well as the value; the terms are nonnegative. The intermediate
sums over words are unconditional sums in `ℝ≥0∞`. The hypothesis `c ≥ 2` is not needed: for
`c < 2` the `r`-th raw letter of every list of `𝒞_ω(c, o, r)` is `c`, which has weight `ϖ(c) = 0`,
so both sides vanish.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The words `w ∈ ℤ^k` with letters at least `2` and letter sum `t`, written as lists, have
total weight `∑_w ∏ᵢ ϖ(wᵢ) = 𝖱(k, t)`. -/
theorem tsum_ofReal_prod_varpi_rawWords (k : ℕ) (t : ℤ) :
    ∑' w : {w : List ℤ // w.length = k ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = t},
      ENNReal.ofReal (w.1.map varpi).prod = ENNReal.ofReal (rawMass k t) := by
  let F : {c : Fin k → ℤ // c ∈ rawWords k t} →
      {w : List ℤ // w.length = k ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = t} := fun c =>
    ⟨List.ofFn c.1, List.length_ofFn, fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact (mem_rawWords.1 c.2).1 i,
      by rw [List.sum_ofFn]; exact (mem_rawWords.1 c.2).2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun c c' h => Subtype.ext (List.ofFn_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨w, hl, h2, hs⟩
    subst hl
    refine ⟨⟨w.get, mem_rawWords.2 ⟨fun i => h2 _ (List.get_mem w i), ?_⟩⟩,
      Subtype.ext (List.ofFn_get w)⟩
    rw [← List.sum_ofFn, List.ofFn_get]
    exact hs
  rw [← (Equiv.ofBijective F hF).tsum_eq]
  simp only [Equiv.ofBijective_apply, F, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
  rw [Finset.tsum_subtype (rawWords k t) (fun c => ENNReal.ofReal (∏ i, varpi (c i))), rawMass,
    ENNReal.ofReal_sum_of_nonneg fun c _ => Finset.prod_nonneg fun i _ => varpi_nonneg _]

/-- The suffix words of a crossing letter have total weight `∑_{u ∈ 𝒮_c} ∏ᵢ ϖ(uᵢ) = 1`. -/
theorem tsum_ofReal_prod_varpi_c3SuffixWords (c : ℤ) :
    ∑' u : c3SuffixWords c, ENNReal.ofReal (u.1.map varpi).prod = 1 := by
  by_cases hc : c ∈ ({4, 5} : Set ℤ)
  · rw [c3SuffixWords_of_mem hc,
      tsum_singleton ([] : List ℤ) (fun u : List ℤ => ENNReal.ofReal (u.map varpi).prod)]
    simp
  have hfin (j : ℕ) (l : ℤ) : (holdWords j l).Finite :=
    (rawWords j l).finite_toSet.subset fun w hw => mem_rawWords.2 ⟨hw.1, hw.2.2.2⟩
  let G : (Σ x : ℕ × ℤ, holdWords (x.1 + 1) x.2) → c3SuffixWords c := fun p =>
    ⟨List.ofFn p.2.1, by
      rw [c3SuffixWords_of_notMem hc]
      exact Set.mem_iUnion₂.2 ⟨p.1.1 + 1, by omega, Set.mem_iUnion.2 ⟨p.1.2, p.2.1, p.2.2, rfl⟩⟩⟩
  have hG : Function.Bijective G := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨m, l⟩, w, hw⟩ ⟨⟨m', l'⟩, w', hw'⟩ h
      have h1 : List.ofFn w = List.ofFn w' := congrArg Subtype.val h
      have hm : m = m' := by simpa using congrArg List.length h1
      subst hm
      obtain rfl : w = w' := List.ofFn_injective h1
      obtain rfl : l = l' := (holdWords_sum_eq hw).symm.trans (holdWords_sum_eq hw')
      rfl
    · rintro ⟨u, hu⟩
      rw [c3SuffixWords_of_notMem hc] at hu
      simp only [Set.mem_iUnion, Set.mem_image] at hu
      obtain ⟨j, hj, l, w, hw, rfl⟩ := hu
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      exact ⟨⟨(m, l), w, hw⟩, rfl⟩
  have hinner (x : ℕ × ℤ) :
      ∑' w : holdWords (x.1 + 1) x.2, ENNReal.ofReal (∏ i, varpi (w.1 i)) =
        ENNReal.ofReal (holdLaw (x.1 + 1) x.2) := by
    have := (hfin (x.1 + 1) x.2).to_subtype
    rw [holdLaw_def, ENNReal.ofReal_tsum_of_nonneg
      (fun _ => Finset.prod_nonneg fun _ _ => varpi_nonneg _) Summable.of_finite]
  have hsum : HasSum (fun x : ℕ × ℤ => holdLaw (x.1 + 1) x.2) 1 := by
    have := bkPointsEquiv.hasSum_iff.2 hasSum_holdLaw_bkPoints
    convert this using 2 with x
    simp [bkPointsEquiv]
  rw [← (Equiv.ofBijective G hG).tsum_eq, ENNReal.tsum_sigma']
  simp only [Equiv.ofBijective_apply, G, List.map_ofFn, List.prod_ofFn, Function.comp_apply,
    hinner]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => holdLaw_nonneg _ _) hsum.summable, hsum.tsum_eq,
    ENNReal.ofReal_one]

/-- For `c < 2`, every list of `𝒞_ω(c, o, r)` has weight `0`: its `r`-th raw letter is `c`. -/
theorem trListWeight_eq_zero_of_mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ} (hc : c < 2)
    (hr : 1 ≤ r) {π : List (List ℤ × ℤ)} (hπ : π ∈ c3CrossingSet ω c o r) :
    trListWeight π = 0 := by
  obtain ⟨-, hrM, hpred, hσ⟩ := hπ
  have h0 := chBlockPath_fst_nonneg π π.length
  have hM := toNat_chBlockPath_fst π
  have hlt : r - 1 < (π.flatMap fun b => b.1 ++ [b.2]).length := by omega
  have hsucc := trRawSum_succ π hlt
  rw [Nat.sub_add_cancel hr, hpred, hσ] at hsucc
  have hz : (π.flatMap fun b => b.1 ++ [b.2])[r - 1] = c := by linarith
  have hmem := List.getElem_mem hlt
  rw [hz, List.mem_flatMap] at hmem
  obtain ⟨b, hb, hcb⟩ := hmem
  rw [trListWeight_eq_zero_iff]
  refine ⟨b, hb, ?_⟩
  rw [List.mem_append, List.mem_singleton] at hcb
  rcases hcb with h | h
  · exact mul_eq_zero_of_right _
      (List.prod_eq_zero (List.mem_map.2 ⟨c, h, varpiIn_of_le_one (by omega)⟩))
  · exact mul_eq_zero_of_left (h ▸ varpi_of_le_one (by omega)) _

/-- **Mass of the first raw crossing sets.** For every `ω ∈ ℕ` and all integers `c, o, r` with
`1 ≤ o ≤ c` and `r ≥ 1`, the series `∑_{π ∈ 𝒞_ω(c, o, r)} bw^⊗(π)` converges to
`ϖ(c) 𝖱(r - 1, ω + o - c)`. -/
@[collatz_pos_dens "lem_c3_crossing_mass"]
theorem hasSum_trListWeight_c3CrossingSet (ω : ℕ) {c o : ℤ} {r : ℕ} (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) :
    HasSum (fun π : c3CrossingSet ω c o r ↦ trListWeight π.1)
      (varpi c * rawMass (r - 1) (ω + o - c)) := by
  by_cases hc : 2 ≤ c
  · have hf (π : c3CrossingSet ω c o r) : 0 ≤ trListWeight π.1 := trListWeight_nonneg _
    have hx : 0 ≤ varpi c * rawMass (r - 1) (ω + o - c) :=
      mul_nonneg (varpi_nonneg c) (rawMass_nonneg _ _)
    have key := tsum_c3CrossingSet_mul_eq ω hc ho hoc hr fun _ => 1
    simp only [mul_one, ENNReal.tsum_mul_left, tsum_ofReal_prod_varpi_c3SuffixWords,
      tsum_ofReal_prod_varpi_rawWords] at key
    rw [← ENNReal.ofReal_mul (varpi_nonneg c)] at key
    have hs : Summable fun π : c3CrossingSet ω c o r ↦ trListWeight π.1 := by
      have := ENNReal.summable_toReal (key ▸ ENNReal.ofReal_ne_top)
      simpa [ENNReal.toReal_ofReal (hf _)] using this
    rw [← ENNReal.ofReal_tsum_of_nonneg hf hs,
      ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hf) hx] at key
    exact key ▸ hs.hasSum
  · rw [varpi_of_le_one (by omega), zero_mul]
    convert hasSum_zero with π
    exact trListWeight_eq_zero_of_mem_c3CrossingSet (by omega) hr π.2

/-- **Mass of the first raw crossing sets**, as a `tsum`:
`∑_{π ∈ 𝒞_ω(c, o, r)} bw^⊗(π) = ϖ(c) 𝖱(r - 1, ω + o - c)`. -/
theorem tsum_trListWeight_c3CrossingSet (ω : ℕ) {c o : ℤ} {r : ℕ} (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) :
    ∑' π : c3CrossingSet ω c o r, trListWeight π.1 = varpi c * rawMass (r - 1) (ω + o - c) :=
  (hasSum_trListWeight_c3CrossingSet ω ho hoc hr).tsum_eq

end CollatzPosDens
