/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3InitException
public import CollatzPosDens.Case3.C3CrossingMass
public import CollatzPosDens.Case3.C3CrossingPartition
public import CollatzPosDens.Case3.C3CrossingTail
public import CollatzPosDens.Case3.C3NarrowRow
public import CollatzPosDens.Case3.C3PascalSecondTail
public import CollatzPosDens.Renewal.RnPascalTail
public import CollatzPosDens.Renewal.RnRawOddSum
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.StoppingTrace.TrPassageLaw

/-!
# Mass of the common initial exception

Let `ι ∈ 𝔍` be a Fourier index and `ω ≥ 12500000` an integer. The common initial exception
`𝓑_init(ι, ω)` carries total weight
`∑_{π ∈ 𝓑_init(ι, ω)} bw^⊗(π) ≤ (11/16)^{H_pk(ι)} + 2161/2^127 + 148/ω`.

Write `g = ⌊9ω/32⌋` and `m(c, o, r) = ϖ(c) 𝖱(r - 1, ω + o - c)`, the mass of the first raw
crossing set `𝒞_ω(c, o, r)`, for `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1`. These sets partition `Π_ω`, which
has total weight `1`, so `∑ m(c, o, r) ≤ 1`. By the union bound the weight of `𝓑_init(ι, ω)` is
at most `Σ₁ + Σ₂ + Σ₃`, where:

* `Σ₁` is the weight of the lists of the crossing sets whose raw word runs more than
  `H_pk(ι)` letters past the crossing. For `c ∉ {4, 5}` this is `(11/16)^{H_pk(ι)} m(c, o, r)`;
  for `c ∈ {4, 5}` the raw word ends at the crossing, and the weight is `0`.
  Hence `Σ₁ ≤ (11/16)^{H_pk(ι)}`.
* `Σ₂ = ∑_{c > 128} ∑_{o, r} m(c, o, r)`. Since `∑_{k ≥ 0} 𝖱(k, t) ≤ [t = 0] + 1/4` and at most
  one of the heights `ω + o - c`, `1 ≤ o ≤ c`, vanishes, `∑_{o, r} m(c, o, r) ≤ ϖ(c) (1 + c/4)`,
  and the Pascal tails give `Σ₂ ≤ 129 · 2^{-128} + (128² + 3 · 128 + 4) 2^{-130} = 2161/2^127`.
* `Σ₃ = ∑_{2 ≤ c ≤ 128} ∑_o ∑_{r > g} m(c, o, r)`. Here `ω - 127 ≤ ω + o - c ≤ ω`, so the late
  tails of the raw-prefix rows bound each sum over `r` by `37/ω`, and
  `Σ₃ ≤ (37/ω) ∑_c c ϖ(c) = 148/ω`.

## Main results

* `CollatzPosDens.tsum_ofReal_rawMass_le`: `∑_{k ≥ 0} 𝖱(k, t) ≤ [t = 0] + 1/4`.
* `CollatzPosDens.tsum_ofReal_trListWeight_c3CrossingSet_tail_le`: the lists of `𝒞_ω(c, o, r)`
  running more than `H` letters past the crossing weigh at most
  `ϖ(c) 𝖱(r - 1, ω + o - c) (11/16)^H`, for every crossing letter `c`.
* `CollatzPosDens.tsum_ofReal_varpi_mul_rawMass_le_one`: the crossing masses sum to at most `1`.
* `CollatzPosDens.tsum_ofReal_trListWeight_c3InitException_le`: the bound, as a sum in `ℝ≥0∞`.
* `CollatzPosDens.summable_trListWeight_c3InitException`: the weights on `𝓑_init(ι, ω)` are
  summable.
* `CollatzPosDens.tsum_trListWeight_c3InitException_le`: the bound, as a sum in `ℝ`.

## Implementation notes

The sums over sets of passage lists and over triples `(c, o, r) ∈ ℤ × ℤ × ℕ` are unconditional
sums in `ℝ≥0∞`, where every family is summable and the union bound holds without further
hypotheses; the real form follows. The index `r` is a natural number and `⌊9ω/32⌋` is the
natural number division `9 * ω / 32`, as in `c3InitException`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset
open scoped ENNReal

/-- The raw-prefix masses of all lengths at height `t` sum to at most `[t = 0] + 1/4`:
`𝖱(0, t) = [t = 0]`, and `∑_{k ≥ 1} 𝖱(k, t)` is `1/4` for `t ≥ 2` and `0` for `t < 2`. -/
theorem tsum_ofReal_rawMass_le (t : ℤ) :
    ∑' k : ℕ, ENNReal.ofReal (rawMass k t) ≤
      ENNReal.ofReal ((if t = 0 then 1 else 0) + 1 / 4) := by
  rw [tsum_eq_zero_add' ENNReal.summable, rawMass_zero,
    ENNReal.ofReal_add (by split_ifs <;> norm_num) (by norm_num)]
  gcongr
  by_cases ht : 2 ≤ t
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => rawMass_nonneg _ _)
      (hasSum_rawMass_succ ht).summable, (hasSum_rawMass_succ ht).tsum_eq]
  · simp only [rawMass_succ_of_lt_two _ (not_le.1 ht), ENNReal.ofReal_zero, tsum_zero, zero_le]

/-- Shifting the length index: `∑_{r ≥ 1} 𝖱(r - 1, t) = ∑_{k ≥ 0} 𝖱(k, t)`. -/
private lemma tsum_ite_one_le_ofReal_rawMass (t : ℤ) :
    ∑' r : ℕ, (if 1 ≤ r then ENNReal.ofReal (rawMass (r - 1) t) else 0) =
      ∑' k : ℕ, ENNReal.ofReal (rawMass k t) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp

/-- An unconditional sum over `ℤ × ℤ × ℕ` in `ℝ≥0∞` is an iterated sum. -/
private lemma tsum_triple (F : ℤ → ℤ → ℕ → ℝ≥0∞) :
    ∑' t : ℤ × ℤ × ℕ, F t.1 t.2.1 t.2.2 = ∑' c, ∑' o, ∑' r, F c o r :=
  (ENNReal.tsum_prod (f := fun (c : ℤ) (p : ℤ × ℕ) => F c p.1 p.2)).trans
    (tsum_congr fun c => ENNReal.tsum_prod (f := fun (o : ℤ) (r : ℕ) => F c o r))

/-- A sum over `{x | P ∧ x ∈ s}` is the sum over `s` if `P` holds, and `0` otherwise. -/
private lemma tsum_setOf_and {α : Type*} (f : α → ℝ≥0∞) (P : Prop) [Decidable P] (s : Set α) :
    ∑' x : {x | P ∧ x ∈ s}, f x = if P then ∑' x : s, f x else 0 := by
  by_cases hP : P
  · have hs : {x | P ∧ x ∈ s} = s := Set.ext fun x => by simp [hP]
    rw [hs]
    simp [hP]
  · simp [hP]

/-- The weight of a first raw crossing set, in `ℝ≥0∞`. -/
private lemma tsum_ofReal_trListWeight_c3CrossingSet (ω : ℕ) {c o : ℤ} {r : ℕ} (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) :
    ∑' π : c3CrossingSet ω c o r, ENNReal.ofReal (trListWeight π.1) =
      ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun π => trListWeight_nonneg _)
    (hasSum_trListWeight_c3CrossingSet ω ho hoc hr).summable,
    (hasSum_trListWeight_c3CrossingSet ω ho hoc hr).tsum_eq]

/-- The lists of `𝒞_ω(c, o, r)` whose raw word runs more than `H` letters past the crossing
weigh at most `ϖ(c) 𝖱(r - 1, ω + o - c) (11/16)^H`, for every crossing letter `c`: for
`c ∉ {4, 5}` this is `hasSum_trListWeight_c3CrossingSet_tail`, and for `c ∈ {4, 5}` the raw word
ends at the crossing, so the weight is `0`. -/
theorem tsum_ofReal_trListWeight_c3CrossingSet_tail_le (ω : ℕ) {c o : ℤ} {r : ℕ} (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) (H : ℕ) :
    ∑' π : {π ∈ c3CrossingSet ω c o r | (H : ℤ) < (chBlockPath π π.length).1 - r},
        ENNReal.ofReal (trListWeight π.1) ≤
      ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) * ENNReal.ofReal ((11 / 16) ^ H) := by
  set S := {π ∈ c3CrossingSet ω c o r | (H : ℤ) < (chBlockPath π π.length).1 - r}
  by_cases hc45 : c ∈ ({4, 5} : Set ℤ)
  · have hc : 2 ≤ c := by
      rcases hc45 with h | h <;> simp_all
    let Ψ : List ℤ → ℝ≥0∞ := fun z => if (H : ℤ) < (z.length : ℤ) - r then 1 else 0
    have key := tsum_c3CrossingSet_mul_eq ω hc ho hoc hr Ψ
    have hL : ∑' π : c3CrossingSet ω c o r,
        ENNReal.ofReal (trListWeight π.1) * Ψ (c3RawWord π.1) =
          ∑' π : S, ENNReal.ofReal (trListWeight π.1) := by
      rw [tsum_subtype (c3CrossingSet ω c o r)
          (fun π => ENNReal.ofReal (trListWeight π) * Ψ (c3RawWord π)),
        tsum_subtype S (fun π => ENNReal.ofReal (trListWeight π))]
      refine tsum_congr fun π => ?_
      have hlen : ((c3RawWord π).length : ℤ) = (chBlockPath π π.length).1 := by
        rw [length_c3RawWord, Int.toNat_of_nonneg (chBlockPath_fst_nonneg _ _)]
      by_cases hπ : π ∈ c3CrossingSet ω c o r
      · rw [Set.indicator_of_mem hπ]
        by_cases hH : (H : ℤ) < (chBlockPath π π.length).1 - r
        · rw [Set.indicator_of_mem (show π ∈ S from ⟨hπ, hH⟩)]
          simp [Ψ, hlen, hH]
        · rw [Set.indicator_of_notMem (show π ∉ S from fun h => hH h.2)]
          simp [Ψ, hlen, hH]
      · rw [Set.indicator_of_notMem hπ, Set.indicator_of_notMem (show π ∉ S from fun h => hπ h.1)]
    have hR : ∀ w : {w : List ℤ // w.length = r - 1 ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = ω + o - c},
        ∑' u : c3SuffixWords c, ENNReal.ofReal (w.1.map varpi).prod *
          ENNReal.ofReal (u.1.map varpi).prod * Ψ (w.1 ++ c :: u.1) = 0 := by
      intro w
      refine ENNReal.tsum_eq_zero.2 fun u => ?_
      have hu : u.1 = [] := by
        have h : u.1 ∈ ({[]} : Set (List ℤ)) := c3SuffixWords_of_mem hc45 ▸ u.2
        exact h
      have : ¬ (H : ℤ) < (((w.1 ++ c :: u.1).length : ℕ) : ℤ) - r := by
        simp only [hu, List.length_append, List.length_cons, List.length_nil, w.2.1]
        omega
      simp only [Ψ, this, ite_false, mul_zero]
    simp only [hR, tsum_zero, mul_zero, hL] at key
    rw [key]
    exact zero_le
  · rw [← ENNReal.ofReal_mul (mul_nonneg (varpi_nonneg c) (rawMass_nonneg _ _)),
      ← ENNReal.ofReal_tsum_of_nonneg (fun π => trListWeight_nonneg _)
        (hasSum_trListWeight_c3CrossingSet_tail ω hc45 ho hoc hr H).summable,
      (hasSum_trListWeight_c3CrossingSet_tail ω hc45 ho hoc hr H).tsum_eq]

/-- The first raw crossing sets with `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1` have total weight at most `1`:
they are pairwise disjoint subsets of `Π_ω`, which has total weight `1`. -/
theorem tsum_ofReal_varpi_mul_rawMass_le_one (ω : ℕ) :
    ∑' c : ℤ, ∑' o : ℤ, ∑' r : ℕ, (if 2 ≤ c ∧ 1 ≤ o ∧ o ≤ c ∧ 1 ≤ r then
        ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) else 0) ≤ 1 := by
  classical
  set V : Set (ℤ × ℤ × ℕ) := {t | 2 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2}
  let C : V → Set (List (List ℤ × ℤ)) := fun t => c3CrossingSet ω t.1.1 t.1.2.1 t.1.2.2
  let f : List (List ℤ × ℤ) → ℝ≥0∞ := fun π => ENNReal.ofReal (trListWeight π)
  rw [← tsum_triple (fun c o r => if 2 ≤ c ∧ 1 ≤ o ∧ o ≤ c ∧ 1 ≤ r then
      ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) else 0)]
  have h1 : ∑' t : ℤ × ℤ × ℕ, (if 2 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2 then
        ENNReal.ofReal (varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1)) else 0) =
      ∑' t : V, ∑' π : C t, f π := by
    refine Eq.trans ?_ (tsum_congr fun t : V =>
      (tsum_ofReal_trListWeight_c3CrossingSet ω t.2.2.1 t.2.2.2.1 t.2.2.2.2).symm)
    rw [tsum_subtype V
        (fun t => ENNReal.ofReal (varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1)))]
    refine tsum_congr fun t => ?_
    simp only [Set.indicator_apply, V, Set.mem_ofPred_eq]
  let φ : (Σ t : V, C t) → trPassage ω := fun p =>
    ⟨p.2.1, c3CrossingSet_subset_trPassage _ _ _ _ p.2.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨⟨t, ht⟩, π, hπ⟩ ⟨⟨t', ht'⟩, π', hπ'⟩ h
    have hππ : π = π' := congrArg Subtype.val h
    subst hππ
    obtain rfl : t = t' := (existsUnique_mem_c3CrossingSet
      (c3CrossingSet_subset_trPassage _ _ _ _ hπ)).unique ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2, hπ⟩
        ⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2, hπ'⟩
    rfl
  have hpass : ∑' π : trPassage ω, f π = 1 := by
    have := tsum_trPassage_eq_tsum_firstPassageLaw ω fun _ => 1
    simp only [mul_one] at this
    rw [this, ← ENNReal.ofReal_tsum_of_nonneg (firstPassageLaw_nonneg ω)
      (summable_firstPassageLaw ω), tsum_firstPassageLaw, ENNReal.ofReal_one]
  rw [h1, ← ENNReal.tsum_sigma' (fun p : Σ t : V, C t => f p.2.1), ← hpass]
  exact ENNReal.tsum_comp_le_tsum_of_injective hφ (fun π : trPassage ω => f π.1)

/-- Factoring a row: for a crossing letter `c`, the masses `ϖ(c) 𝖱(r - 1, ω + o - c)` over
`1 ≤ o ≤ c` and the indices `r` satisfying `Q` sum to at most `ϖ(c) ∑_{o=1}^c b(o)`, if the
sum over `r` at each offset `o` is at most `b(o)`. -/
private lemma tsum_tsum_ite_le (ω : ℕ) (c : ℤ) (Q : ℕ → Prop) [DecidablePred Q] (b : ℤ → ℝ)
    (hb : ∀ o ∈ Icc 1 c, 0 ≤ b o)
    (h : ∀ o ∈ Icc 1 c, ∑' r : ℕ, (if Q r then ENNReal.ofReal (rawMass (r - 1) (ω + o - c))
      else 0) ≤ ENNReal.ofReal (b o)) :
    ∑' o : ℤ, ∑' r : ℕ, (if (1 ≤ o ∧ o ≤ c) ∧ Q r then
        ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) else 0) ≤
      ENNReal.ofReal (varpi c * ∑ o ∈ Icc 1 c, b o) := by
  have hrow (o : ℤ) : ∑' r : ℕ, (if (1 ≤ o ∧ o ≤ c) ∧ Q r then
        ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) else 0) =
      (↑(Icc 1 c) : Set ℤ).indicator (fun o => ENNReal.ofReal (varpi c) *
        ∑' r : ℕ, if Q r then ENNReal.ofReal (rawMass (r - 1) (ω + o - c)) else 0) o := by
    by_cases ho : 1 ≤ o ∧ o ≤ c
    · rw [Set.indicator_of_mem (by simpa using ho), ← ENNReal.tsum_mul_left]
      refine tsum_congr fun r => ?_
      by_cases hr : Q r <;> simp [ho, hr, ENNReal.ofReal_mul (varpi_nonneg c)]
    · rw [Set.indicator_of_notMem (by simpa using ho)]
      simp [ho]
  simp_rw [hrow]
  rw [← sum_eq_tsum_indicator, ENNReal.ofReal_mul (varpi_nonneg c),
    ENNReal.ofReal_sum_of_nonneg hb, mul_sum]
  exact sum_le_sum fun o ho => by gcongr; exact h o ho

/-- Among the offsets `1 ≤ o ≤ c`, at most one height `ω + o - c` vanishes:
`∑_{o=1}^c ([ω + o - c = 0] + 1/4) ≤ 1 + c/4`. -/
private lemma sum_Icc_ite_add_le (ω : ℕ) {c : ℤ} (hc : 0 ≤ c) :
    ∑ o ∈ Icc 1 c, ((if (ω : ℤ) + o - c = 0 then 1 else 0) + 1 / 4 : ℝ) ≤ 1 + c / 4 := by
  have h1 : ∑ o ∈ Icc 1 c, (if (ω : ℤ) + o - c = 0 then (1 : ℝ) else 0) ≤ 1 := by
    have : ∀ o : ℤ, ((ω : ℤ) + o - c = 0 ↔ o = c - ω) := fun o => by omega
    simp_rw [this]
    rw [sum_ite_eq']
    split_ifs <;> norm_num
  have h2 : ((c.toNat : ℕ) : ℝ) = c := by exact_mod_cast Int.toNat_of_nonneg hc
  rw [sum_add_distrib, sum_const, Int.card_Icc, nsmul_eq_mul, show c + 1 - 1 = c by ring, h2]
  linarith

/-- The row of a large crossing letter: `∑_{o, r} ϖ(c) 𝖱(r - 1, ω + o - c) ≤ ϖ(c) (1 + c/4)`. -/
private lemma tsum_row_le (ω : ℕ) {c : ℤ} (hc : 0 ≤ c) :
    ∑' o : ℤ, ∑' r : ℕ, (if (1 ≤ o ∧ o ≤ c) ∧ 1 ≤ r then
        ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) else 0) ≤
      ENNReal.ofReal (varpi c + 1 / 4 * (c * varpi c)) := by
  refine (tsum_tsum_ite_le ω c (1 ≤ ·) (fun o => (if (ω : ℤ) + o - c = 0 then 1 else 0) + 1 / 4)
    (fun o _ => by split_ifs <;> norm_num) fun o _ => ?_).trans ?_
  · rw [tsum_ite_one_le_ofReal_rawMass]
    exact tsum_ofReal_rawMass_le _
  · apply ENNReal.ofReal_le_ofReal
    have := sum_Icc_ite_add_le ω hc
    nlinarith [varpi_nonneg c]

/-- The late part of the row of a small crossing letter `2 ≤ c ≤ 128`:
`∑_o ∑_{r > ⌊9ω/32⌋} ϖ(c) 𝖱(r - 1, ω + o - c) ≤ c ϖ(c) · 37/ω`. -/
private lemma tsum_row_late_le {ω : ℕ} (hω : 12500000 ≤ ω) {c : ℤ} (hc : 2 ≤ c) (hc' : c ≤ 128) :
    ∑' o : ℤ, ∑' r : ℕ, (if (1 ≤ o ∧ o ≤ c) ∧ 9 * ω / 32 < r then
        ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c)) else 0) ≤
      ENNReal.ofReal (c * varpi c * (37 / ω)) := by
  have hg : ⌊9 * ((ω : ℤ) : ℝ) / 32⌋₊ = 9 * ω / 32 := by
    have := Nat.floor_div_eq_div (K := ℝ) (9 * ω) 32
    push_cast at this
    rw [Int.cast_natCast, this]
  refine (tsum_tsum_ite_le ω c (9 * ω / 32 < ·) (fun _ => 37 / (ω : ℝ))
    (fun _ _ => by positivity) fun o ho => ?_).trans (le_of_eq ?_)
  · rw [mem_Icc] at ho
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    rw [← sum_filter, ← ENNReal.ofReal_sum_of_nonneg fun _ _ => rawMass_nonneg _ _]
    apply ENNReal.ofReal_le_ofReal
    have := sum_rawMass_late_tail_le (ω := (ω : ℤ)) (l := ω + o - c) (by exact_mod_cast hω)
      (by omega) (by omega) ((range n).filter (9 * ω / 32 < ·)) fun r hr => by
        rw [hg]; exact (mem_filter.1 hr).2
    simpa using this
  · have h2 : ((c.toNat : ℕ) : ℝ) = c := by exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ c)
    rw [sum_const, Int.card_Icc, nsmul_eq_mul, show c + 1 - 1 = c by ring, h2]
    ring_nf

/-- **Mass of the common initial exception.** For every Fourier index `ι` and every integer
`ω ≥ 12500000`,
`∑_{π ∈ 𝓑_init(ι, ω)} bw^⊗(π) ≤ (11/16)^{H_pk(ι)} + 2161/2^127 + 148/ω`, as a sum in
`ℝ≥0∞`. -/
@[collatz_pos_dens "lem_c3_init_exception_mass"]
theorem tsum_ofReal_trListWeight_c3InitException_le (ι : FIndex) {ω : ℕ} (hω : 12500000 ≤ ω) :
    ∑' π : c3InitException ι ω, ENNReal.ofReal (trListWeight π.1) ≤
      ENNReal.ofReal ((11 / 16) ^ Hpack ι + 2161 / 2 ^ 127 + 148 / ω) := by
  classical
  set f : List (List ℤ × ℤ) → ℝ≥0∞ := fun π => ENNReal.ofReal (trListWeight π) with hf
  set g : ℕ := 9 * ω / 32 with hg
  set q : ℝ := (11 / 16) ^ Hpack ι with hq
  let m : ℤ → ℤ → ℕ → ℝ≥0∞ := fun c o r =>
    ENNReal.ofReal (varpi c * rawMass (r - 1) (ω + o - c))
  let E : ℤ × ℤ × ℕ → Set (List (List ℤ × ℤ)) := fun t =>
    {π | (2 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2) ∧
      π ∈ c3CrossingSet ω t.1 t.2.1 t.2.2 ∧
      ((Hpack ι : ℤ) < (chBlockPath π π.length).1 - t.2.2 ∨ 128 < t.1 ∨ g < t.2.2)}
  let b1 : ℤ → ℤ → ℕ → ℝ≥0∞ := fun c o r =>
    (if 2 ≤ c ∧ 1 ≤ o ∧ o ≤ c ∧ 1 ≤ r then m c o r else 0) * ENNReal.ofReal q
  let b2 : ℤ → ℤ → ℕ → ℝ≥0∞ := fun c o r =>
    if 2 ≤ c ∧ 128 < c then (if (1 ≤ o ∧ o ≤ c) ∧ 1 ≤ r then m c o r else 0) else 0
  let b3 : ℤ → ℤ → ℕ → ℝ≥0∞ := fun c o r =>
    if 2 ≤ c ∧ c ≤ 128 then (if (1 ≤ o ∧ o ≤ c) ∧ g < r then m c o r else 0) else 0
  have hsub : c3InitException ι ω ⊆ ⋃ t, E t := by
    rintro π ⟨-, c, o, r, hc, ho, hoc, hr, hπ, hbad⟩
    exact Set.mem_iUnion.2 ⟨(c, o, r), ⟨hc, ho, hoc, hr⟩, hπ, hbad⟩
  have hE : ∀ t : ℤ × ℤ × ℕ, ∑' π : E t, f π ≤
      b1 t.1 t.2.1 t.2.2 + b2 t.1 t.2.1 t.2.2 + b3 t.1 t.2.1 t.2.2 := by
    rintro ⟨c, o, r⟩
    by_cases hv : 2 ≤ c ∧ 1 ≤ o ∧ o ≤ c ∧ 1 ≤ r
    · obtain ⟨hc, ho, hoc, hr⟩ := hv
      set C := c3CrossingSet ω c o r
      have hsub' : E (c, o, r) ⊆
          {π ∈ C | (Hpack ι : ℤ) < (chBlockPath π π.length).1 - r} ∪
            ({π | 128 < c ∧ π ∈ C} ∪ {π | (c ≤ 128 ∧ g < r) ∧ π ∈ C}) := by
        rintro π ⟨-, hπ, hbad⟩
        rcases hbad with h | h | h
        · exact Or.inl ⟨hπ, h⟩
        · exact Or.inr (Or.inl ⟨h, hπ⟩)
        · by_cases h' : 128 < c
          · exact Or.inr (Or.inl ⟨h', hπ⟩)
          · exact Or.inr (Or.inr ⟨⟨not_lt.1 h', h⟩, hπ⟩)
      refine (ENNReal.tsum_mono_subtype f hsub').trans ((ENNReal.tsum_union_le f _ _).trans ?_)
      rw [add_assoc]
      gcongr
      · have := tsum_ofReal_trListWeight_c3CrossingSet_tail_le ω ho hoc hr (Hpack ι)
        simpa [b1, m, hc, ho, hoc, hr] using this
      · refine (ENNReal.tsum_union_le f _ _).trans ?_
        rw [tsum_setOf_and, tsum_setOf_and, tsum_ofReal_trListWeight_c3CrossingSet ω ho hoc hr]
        gcongr
        · by_cases h : 128 < c <;> simp [b2, m, h, hc, ho, hoc, hr]
        · by_cases h : c ≤ 128 ∧ g < r
          · simp [b3, m, h, hc, ho, hoc]
          · simp [h]
    · have hempty : E (c, o, r) = ∅ := Set.eq_empty_of_forall_notMem fun π h => hv h.1
      rw [hempty, tsum_empty]
      exact zero_le
  have hA : ∑' c, ∑' o, ∑' r, b1 c o r ≤ ENNReal.ofReal q := by
    simp only [b1, ENNReal.tsum_mul_right]
    calc _ ≤ 1 * ENNReal.ofReal q := by gcongr; exact tsum_ofReal_varpi_mul_rawMass_le_one ω
      _ = ENNReal.ofReal q := one_mul _
  have hB : ∑' c, ∑' o, ∑' r, b2 c o r ≤ ENNReal.ofReal (2161 / 2 ^ 127) := by
    set F : ℤ → ℝ := fun c => (Set.Ioi ((128 : ℕ) : ℤ)).indicator varpi c +
      1 / 4 * (Set.Ioi ((128 : ℕ) : ℤ)).indicator (fun b => (b : ℝ) * varpi b) c with hF
    have hFsum : HasSum F (2161 / 2 ^ 127) := by
      have := (hasSum_varpi_indicator_Ioi 128).add
        ((hasSum_mul_varpi_indicator_Ioi 128).mul_left (1 / 4))
      convert this using 1
      simp only [zpow_neg, zpow_natCast]
      norm_num
    have hF0 : ∀ c, 0 ≤ F c := fun c => by
      simp only [F, Set.indicator_apply, Set.mem_Ioi]
      split_ifs with h
      · have : (0 : ℝ) ≤ c := by exact_mod_cast (by omega : (0 : ℤ) ≤ c)
        positivity [varpi_nonneg c]
      · norm_num
    calc _ ≤ ∑' c, ENNReal.ofReal (F c) := by
          refine ENNReal.tsum_le_tsum fun c => ?_
          by_cases h : 2 ≤ c ∧ 128 < c
          · simp only [b2, h, and_self, ite_true]
            have hm : c ∈ Set.Ioi ((128 : ℕ) : ℤ) := by simpa using h.2
            simp only [F, Set.indicator_of_mem hm]
            exact tsum_row_le ω (by omega)
          · simp [b2, h]
      _ = ENNReal.ofReal (2161 / 2 ^ 127) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hF0 hFsum.summable, hFsum.tsum_eq]
  have hC : ∑' c, ∑' o, ∑' r, b3 c o r ≤ ENNReal.ofReal (148 / ω) := by
    set F : ℤ → ℝ := fun c =>
      (Set.Ioi ((0 : ℕ) : ℤ)).indicator (fun b => (b : ℝ) * varpi b) c * (37 / ω) with hF
    have hFsum : HasSum F (148 / ω) := by
      have := (hasSum_mul_varpi_indicator_Ioi 0).mul_right (37 / (ω : ℝ))
      convert this using 1
      norm_num
      ring
    have hF0 : ∀ c, 0 ≤ F c := fun c => by
      simp only [F, Set.indicator_apply, Set.mem_Ioi]
      split_ifs with h
      · have : (0 : ℝ) ≤ c := by exact_mod_cast (by omega : (0 : ℤ) ≤ c)
        positivity [varpi_nonneg c]
      · norm_num
    calc _ ≤ ∑' c, ENNReal.ofReal (F c) := by
          refine ENNReal.tsum_le_tsum fun c => ?_
          by_cases h : 2 ≤ c ∧ c ≤ 128
          · simp only [b3, h, and_self, ite_true]
            have hm : c ∈ Set.Ioi ((0 : ℕ) : ℤ) := by simp; omega
            simp only [F, Set.indicator_of_mem hm]
            exact tsum_row_late_le hω h.1 h.2
          · simp [b3, h]
      _ = ENNReal.ofReal (148 / ω) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hF0 hFsum.summable, hFsum.tsum_eq]
  calc ∑' π : c3InitException ι ω, f π ≤ ∑' π : ⋃ t, E t, f π :=
        ENNReal.tsum_mono_subtype f hsub
    _ ≤ ∑' t, ∑' π : E t, f π := ENNReal.tsum_iUnion_le_tsum f E
    _ ≤ ∑' t : ℤ × ℤ × ℕ, (b1 t.1 t.2.1 t.2.2 + b2 t.1 t.2.1 t.2.2 + b3 t.1 t.2.1 t.2.2) :=
        ENNReal.tsum_le_tsum hE
    _ = (∑' c, ∑' o, ∑' r, b1 c o r) + (∑' c, ∑' o, ∑' r, b2 c o r) +
          ∑' c, ∑' o, ∑' r, b3 c o r := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_triple b1, tsum_triple b2, tsum_triple b3]
    _ ≤ ENNReal.ofReal q + ENNReal.ofReal (2161 / 2 ^ 127) + ENNReal.ofReal (148 / ω) := by
        gcongr
    _ = ENNReal.ofReal (q + 2161 / 2 ^ 127 + 148 / ω) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]

/-- For every Fourier index `ι` and `ω ≥ 12500000`, the weights `bw^⊗(π)`, `π ∈ 𝓑_init(ι, ω)`,
are summable. -/
theorem summable_trListWeight_c3InitException (ι : FIndex) {ω : ℕ} (hω : 12500000 ≤ ω) :
    Summable fun π : c3InitException ι ω ↦ trListWeight π.1 := by
  have h := ENNReal.summable_toReal
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tsum_ofReal_trListWeight_c3InitException_le ι hω))
  simpa [ENNReal.toReal_ofReal (trListWeight_nonneg _)] using h

/-- **Mass of the common initial exception.** For every Fourier index `ι` and every integer
`ω ≥ 12500000`,
`∑_{π ∈ 𝓑_init(ι, ω)} bw^⊗(π) ≤ (11/16)^{H_pk(ι)} + 2161/2^127 + 148/ω`; the series
converges by `summable_trListWeight_c3InitException`. -/
@[collatz_pos_dens "lem_c3_init_exception_mass"]
theorem tsum_trListWeight_c3InitException_le (ι : FIndex) {ω : ℕ} (hω : 12500000 ≤ ω) :
    ∑' π : c3InitException ι ω, trListWeight π.1 ≤
      (11 / 16) ^ Hpack ι + 2161 / 2 ^ 127 + 148 / ω := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
    ENNReal.ofReal_tsum_of_nonneg (fun _ => trListWeight_nonneg _)
      (summable_trListWeight_c3InitException ι hω)]
  exact tsum_ofReal_trListWeight_c3InitException_le ι hω

end CollatzPosDens
