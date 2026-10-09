/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpRaw
public import CollatzPosDens.Renewal.RnGreenClosed
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldWords
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnGreenFormula
public import CollatzPosDens.Renewal.RnTerminalSplit

/-!
# The raw-word form of the first-passage law

Let `s ∈ ℕ`, `r ≥ 1` and `ℓ ∈ ℤ` with `ℓ > s`. The first-passage law at `(r, ℓ)` is the total
weight of the raw first-passage words:
`F_s(r, ℓ) = ∑_{c ∈ 𝒟_s(r, ℓ)} ∏_{i=1}^r ϖ(c_i)`.

By the terminal-step decomposition and the closed form of the Green's function,
`F_s(r, ℓ) = ∑_{n < r} ∑_{m = 0}^{s} η(r - n, ℓ - m) 𝒢ᶜˡ(n, m)`. Here `𝒢ᶜˡ(n, m)` is the total
weight of the words of length `n` with letters `≥ 2`, letter sum `m` and last letter in `{4, 5}`
(the empty word if `n = 0`), and `η(r - n, ℓ - m)` is the total weight of the hold words
`𝒞_{r-n, ℓ-m}`. A word `c ∈ 𝒟_s(r, ℓ)` splits uniquely as a concatenation `c = c' c''` of such
words: the split point `n` is the position of the last letter in `{4, 5}` before the final
letter (or `0` if there is none), and then `m = c_1 + ⋯ + c_n ≤ s`. The product of the two sums
is therefore the sum over the words of `𝒟_s(r, ℓ)` with split point `n` and prefix sum `m`.

## Main definitions

* `CollatzPosDens.varpiWordWeight`: the weight `∏_i ϖ(c_i)` of a word.
* `CollatzPosDens.wordPrefixSum`: the prefix sum `c_1 + ⋯ + c_n` of a word.

## Main results

* `CollatzPosDens.firstPassageLaw_eq_sum_firstPassageWords`: the raw-word form
  `F_s(r, ℓ) = ∑_{c ∈ 𝒟_s(r, ℓ)} ∏_i ϖ(c_i)`.
* `CollatzPosDens.wordPrefixSum_append_of_le`, `CollatzPosDens.wordPrefixSum_append_of_ge`: the
  prefix sums of a concatenation `Fin.append a b`.

## Implementation notes

Words are functions `Fin r → ℤ`. The split point of a word is computed as the supremum in `ℕ`
of `i + 1` over the positions `i` with `i + 1 < r` and `c_i ∈ {4, 5}`, and the prefix sum
`c_1 + ⋯ + c_n` as a sum over all positions of the letters at positions `< n`. The
concatenation of words is `Fin.append`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §6.4.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The weight `∏_i ϖ(c_i)` of a word. -/
noncomputable abbrev varpiWordWeight {r : ℕ} (c : Fin r → ℤ) : ℝ := ∏ i, varpi (c i)

/-- The weight of a word is nonnegative. -/
theorem varpiWordWeight_nonneg {r : ℕ} (c : Fin r → ℤ) : 0 ≤ varpiWordWeight c :=
  prod_nonneg fun _ _ ↦ varpi_nonneg _

/-- Words of length `n` with letters `≥ 2`, sum `m` and last letter in `{4, 5}`. -/
private def fpRawGreenWords (n : ℕ) (m : ℤ) : Finset (Fin n → ℤ) :=
  (rawWords n m).filter fun c => ∀ i : Fin n, (i : ℕ) + 1 = n → (c i = 4 ∨ c i = 5)

/-- The hold words `𝒞_{k,l}` as a finite set. -/
private def fpRawHoldWords (k : ℕ) (l : ℤ) : Finset (Fin k → ℤ) :=
  (rawWords k l).filter fun c => ∀ i : Fin k,
    ((i : ℕ) + 1 < k → ¬(c i = 4 ∨ c i = 5)) ∧ ((i : ℕ) + 1 = k → (c i = 4 ∨ c i = 5))

private lemma holdLaw_eq_sum_fpRawHoldWords (k : ℕ) (l : ℤ) :
    holdLaw k l = ∑ c ∈ fpRawHoldWords k l, varpiWordWeight c := by
  have h : holdWords k l = ↑(fpRawHoldWords k l) := by
    ext c
    simp only [mem_holdWords, fpRawHoldWords, coe_filter, Set.mem_ofPred_eq, mem_rawWords,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨h2, hlt, heq, hs⟩ => ⟨⟨h2, hs⟩, fun i => ⟨hlt i, heq i⟩⟩,
      fun ⟨⟨h2, hs⟩, hi⟩ => ⟨h2, fun i => (hi i).1, fun i => (hi i).2, hs⟩⟩
  rw [holdLaw_def, h]
  exact Finset.tsum_subtype' (fpRawHoldWords k l) fun c => ∏ i, varpi (c i)

private lemma greenClosed_eq_sum_fpRawGreenWords (n : ℕ) (m : ℤ) :
    greenClosed n m = ∑ c ∈ fpRawGreenWords n m, varpiWordWeight c := by
  cases n with
  | zero =>
    have : fpRawGreenWords 0 m = rawWords 0 m :=
      filter_true_of_mem fun c _ i => i.elim0
    rw [this, ← rawMass, rawMass_zero]
    simp
  | succ n =>
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, greenClosed_succ, rawMass,
      rawMass, mul_sum, mul_sum,
      ← sum_pair (f := fun a : ℤ => ∑ c ∈ rawWords n (m - a), varpi a * ∏ i, varpi (c i))
      (show (4 : ℤ) ≠ 5 by decide), sum_sigma']
    refine sum_nbij' (fun x => Fin.snoc (α := fun _ => ℤ) x.2 x.1)
      (fun c => ⟨c (Fin.last n), Fin.init c⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨a, d⟩ hx
      simp only [mem_sigma, mem_insert, mem_singleton, mem_rawWords] at hx
      simp only [fpRawGreenWords, mem_filter, mem_rawWords, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last]
      refine ⟨⟨fun i => ?_, by linarith [hx.2.2]⟩, fun i hi => ?_⟩
      · induction i using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last]
          rcases hx.1 with rfl | rfl <;> norm_num
        | cast i => simpa only [Fin.snoc_castSucc] using hx.2.1 i
      · obtain rfl : i = Fin.last n := Fin.ext (by simp; omega)
        simpa only [Fin.snoc_last] using hx.1
    · intro c hc
      simp only [fpRawGreenWords, mem_filter, mem_rawWords, Fin.sum_univ_castSucc] at hc
      simp only [mem_sigma, mem_insert, mem_singleton, mem_rawWords, Fin.init]
      exact ⟨hc.2 _ (by simp), fun i => hc.1.1 _, by linarith [hc.1.2]⟩
    · rintro ⟨a, d⟩ _
      simp
    · intro c _
      simp
    · rintro ⟨a, d⟩ _
      simp [Fin.prod_univ_castSucc, mul_comm]

/-! ### Prefix sums of a word -/

/-- The prefix sum `S_n = c_1 + ⋯ + c_n` of a word, the sum of its letters at positions `< n`. -/
def wordPrefixSum {r : ℕ} (c : Fin r → ℤ) (n : ℕ) : ℤ :=
  ∑ i : Fin r, if (i : ℕ) < n then c i else 0

/-- The empty prefix sum vanishes: `S_0 = 0`. -/
theorem wordPrefixSum_zero {r : ℕ} (c : Fin r → ℤ) : wordPrefixSum c 0 = 0 := by
  simp [wordPrefixSum]

/-- For `n ≥ r`, the prefix sum `S_n` is the total letter sum of the word. -/
theorem wordPrefixSum_of_le {r : ℕ} (c : Fin r → ℤ) {n : ℕ} (hn : r ≤ n) :
    wordPrefixSum c n = ∑ i, c i :=
  sum_congr rfl fun i _ ↦ ite_eq_left (by omega)

/-- For `n < r`, `S_{n+1} = S_n + c_{n+1}`. -/
theorem wordPrefixSum_succ {r : ℕ} (c : Fin r → ℤ) {n : ℕ} (hn : n < r) :
    wordPrefixSum c (n + 1) = wordPrefixSum c n + c ⟨n, hn⟩ := by
  have h : ∀ i : Fin r, (if (i : ℕ) < n + 1 then c i else 0) =
      (if (i : ℕ) < n then c i else 0) + if (⟨n, hn⟩ : Fin r) = i then c i else 0 := by
    intro i
    by_cases h1 : (i : ℕ) < n
    · rw [ite_eq_left (by omega), ite_eq_left h1,
        ite_eq_right (fun h ↦ by rw [← h] at h1; simp at h1)]
      ring
    · by_cases h2 : (i : ℕ) = n
      · obtain rfl : i = ⟨n, hn⟩ := Fin.ext h2
        simp
      · rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right (fun h ↦ h2 (by rw [← h]))]
        ring
  simp only [wordPrefixSum, h, sum_add_distrib, sum_ite_eq, mem_univ, ite_true]

/-- The sum of the letters at positions `≤ i` is the prefix sum `S_{i+1}`. -/
theorem sum_Iic_eq_wordPrefixSum {r : ℕ} (c : Fin r → ℤ) (i : Fin r) :
    ∑ j ∈ Iic i, c j = wordPrefixSum c ((i : ℕ) + 1) := by
  rw [wordPrefixSum, ← sum_filter]
  congr 1
  ext j
  simp only [mem_Iic, mem_filter, mem_univ, true_and, Fin.le_def]
  omega

/-- Prefix sums of a word with letters `≥ 2` are monotone. -/
theorem wordPrefixSum_mono {r : ℕ} (c : Fin r → ℤ) (hc : ∀ i, 2 ≤ c i) {a b : ℕ}
    (hab : a ≤ b) : wordPrefixSum c a ≤ wordPrefixSum c b := by
  refine sum_le_sum fun i _ ↦ ?_
  have := hc i
  split_ifs <;> omega

/-- Prefix sums of a word with letters `≥ 2` are nonnegative. -/
theorem wordPrefixSum_nonneg {r : ℕ} (c : Fin r → ℤ) (hc : ∀ i, 2 ≤ c i) (n : ℕ) :
    0 ≤ wordPrefixSum c n :=
  sum_nonneg fun i _ ↦ by have := hc i; split_ifs <;> omega

/-- Within a word with letters `≥ 2`, `S_a + 2 (b - a) ≤ S_b` for `a ≤ b ≤ r`. -/
theorem wordPrefixSum_add_two_mul_le {r : ℕ} (c : Fin r → ℤ) (h2 : ∀ i, 2 ≤ c i) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ r) : wordPrefixSum c a + 2 * ((b : ℤ) - a) ≤ wordPrefixSum c b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [wordPrefixSum_succ c (by omega)]
    have := ih (by omega)
    have := h2 ⟨n, by omega⟩
    push_cast
    linarith

/-- For a word of length `k + 1`, `S_k` is the sum of all letters but the last. -/
theorem wordPrefixSum_last {k : ℕ} (c : Fin (k + 1) → ℤ) :
    wordPrefixSum c k = ∑ i : Fin k, c i.castSucc := by
  have h1 := wordPrefixSum_succ c (n := k) (by omega)
  rw [wordPrefixSum_of_le c le_rfl, Fin.sum_univ_castSucc] at h1
  have : c ⟨k, by omega⟩ = c (Fin.last k) := rfl
  linarith

/-- For a word of length `n + k`, `S_n` is the sum of its first `n` letters. -/
theorem wordPrefixSum_castAdd {n k : ℕ} (c : Fin (n + k) → ℤ) :
    wordPrefixSum c n = ∑ i, c (Fin.castAdd k i) := by
  simp [wordPrefixSum, Fin.sum_univ_add]

/-- For `n ≤ p`, the prefix sum `S_n` of a concatenation `a b`, with `a` of length `p`, is the
prefix sum `S_n` of `a`. -/
theorem wordPrefixSum_append_of_le {p q : ℕ} (a : Fin p → ℤ) (b : Fin q → ℤ) {n : ℕ}
    (hn : n ≤ p) : wordPrefixSum (Fin.append a b) n = wordPrefixSum a n := by
  rw [wordPrefixSum, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
  have h0 : ∑ i : Fin q, (if p + (i : ℕ) < n then b i else 0) = 0 :=
    sum_eq_zero fun i _ ↦ ite_eq_right (by omega)
  rw [h0, add_zero]
  rfl

/-- For `n ≥ p`, the prefix sum `S_n` of a concatenation `a b`, with `a` of length `p`, is the
letter sum of `a` plus the prefix sum `S_{n-p}` of `b`. -/
theorem wordPrefixSum_append_of_ge {p q : ℕ} (a : Fin p → ℤ) (b : Fin q → ℤ) {n : ℕ}
    (hn : p ≤ n) : wordPrefixSum (Fin.append a b) n = ∑ i, a i + wordPrefixSum b (n - p) := by
  rw [wordPrefixSum, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
  congr 1
  · exact sum_congr rfl fun i _ ↦ ite_eq_left (by omega)
  · refine sum_congr rfl fun i _ ↦ ?_
    simp only [show p + (i : ℕ) < n ↔ (i : ℕ) < n - p by omega]

/-- The prefix sum of a concatenation `c' c''` up to the length of `c'` is the letter sum of
`c'`. -/
theorem wordPrefixSum_append {n k : ℕ} (c' : Fin n → ℤ) (c'' : Fin k → ℤ) :
    wordPrefixSum (Fin.append c' c'') n = ∑ i, c' i := by
  rw [wordPrefixSum_append_of_ge _ _ le_rfl, Nat.sub_self, wordPrefixSum_zero, add_zero]

/-- The split point of a word: the largest `i + 1` with `i + 1 < r` and `c_i ∈ {4, 5}`, or `0`. -/
private def fpRawSplit {r : ℕ} (c : Fin r → ℤ) : ℕ :=
  (univ.filter fun i : Fin r => (i : ℕ) + 1 < r ∧ (c i = 4 ∨ c i = 5)).sup fun i => (i : ℕ) + 1

private lemma fpRawSplit_not_mem {r : ℕ} (c : Fin r → ℤ) (i : Fin r) (hi : fpRawSplit c ≤ i)
    (hr : (i : ℕ) + 1 < r) : ¬(c i = 4 ∨ c i = 5) := by
  intro h
  have : (i : ℕ) + 1 ≤ fpRawSplit c :=
    le_sup (f := fun i : Fin r => (i : ℕ) + 1) (mem_filter.2 ⟨mem_univ _, hr, h⟩)
  omega

private lemma fpRawSplit_mem {r : ℕ} (c : Fin r → ℤ) (i : Fin r) (hi : (i : ℕ) + 1 = fpRawSplit c) :
    c i = 4 ∨ c i = 5 := by
  by_cases hne : (univ.filter fun i : Fin r => (i : ℕ) + 1 < r ∧ (c i = 4 ∨ c i = 5)).Nonempty
  · obtain ⟨j, hj, hjeq⟩ := exists_mem_eq_sup _ hne fun i : Fin r => (i : ℕ) + 1
    obtain rfl : i = j := Fin.ext (by rw [fpRawSplit] at hi; omega)
    exact (mem_filter.1 hj).2.2
  · rw [not_nonempty_iff_eq_empty] at hne
    simp [fpRawSplit, hne] at hi

private lemma fpRawSplit_lt {r : ℕ} (hr : 0 < r) (c : Fin r → ℤ) : fpRawSplit c < r :=
  (Finset.sup_lt_iff (show (⊥ : ℕ) < r from hr)).2 fun _ hi => (mem_filter.1 hi).2.1

private lemma fpRawSplit_eq {r : ℕ} (c : Fin r → ℤ) (n : ℕ) (hn : n < r)
    (h1 : ∀ i : Fin r, n ≤ i → (i : ℕ) + 1 < r → ¬(c i = 4 ∨ c i = 5))
    (h2 : ∀ i : Fin r, (i : ℕ) + 1 = n → (c i = 4 ∨ c i = 5)) : fpRawSplit c = n := by
  refine le_antisymm (Finset.sup_le fun i hi => ?_) ?_
  · have hi := mem_filter.1 hi
    by_contra hlt
    exact h1 i (by omega) hi.2.1 hi.2.2
  · cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      exact le_sup (f := fun i : Fin r => (i : ℕ) + 1)
        (mem_filter.2 ⟨mem_univ (⟨n, by omega⟩ : Fin r), by simp; omega, h2 ⟨n, by omega⟩ rfl⟩)

private lemma fpRawSplit_append {n k : ℕ} (hk : 0 < k) (c' : Fin n → ℤ) (c'' : Fin k → ℤ)
    (hl' : ∀ j : Fin n, (j : ℕ) + 1 = n → c' j = 4 ∨ c' j = 5)
    (hc'' : ∀ j : Fin k, (j : ℕ) + 1 < k → ¬(c'' j = 4 ∨ c'' j = 5)) :
    fpRawSplit (Fin.append c' c'') = n := by
  refine fpRawSplit_eq _ n (by omega) (fun i hi hr => ?_) (fun i hi => ?_)
  · induction i using Fin.addCases with
    | left j => simp at hi; omega
    | right j =>
      rw [Fin.append_right]
      exact hc'' j (by simp at hr; omega)
  · induction i using Fin.addCases with
    | left j =>
      rw [Fin.append_left]
      exact hl' j (by simpa using hi)
    | right j => simp at hi; omega

/-- The words of `𝒟_s(n + k, ℓ)` with split point `n` and prefix sum `m` are the concatenations
of a word of `fpRawGreenWords n m` and a hold word of `𝒞_{k, ℓ - m}`. -/
private lemma sum_fiber_fpRaw (s n k : ℕ) (hk : 0 < k) (ℓ : ℤ) (m : ℕ) (hm : m ≤ s) :
    ∑ c ∈ (firstPassageWords s (n + k) ℓ).filter
        (fun c => (fpRawSplit c, (wordPrefixSum c (fpRawSplit c)).toNat) = (n, m)),
      varpiWordWeight c = greenClosed n m * holdLaw k (ℓ - m) := by
  rw [greenClosed_eq_sum_fpRawGreenWords, holdLaw_eq_sum_fpRawHoldWords, sum_mul_sum,
    ← sum_product' (f := fun a b => varpiWordWeight a * varpiWordWeight b)]
  symm
  refine sum_nbij' (fun x => Fin.append x.1 x.2)
    (fun c => (fun i => c (Fin.castAdd k i), fun j => c (Fin.natAdd n j))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨c', c''⟩ hx
    simp only [mem_product, fpRawGreenWords, fpRawHoldWords, mem_filter, mem_rawWords] at hx
    obtain ⟨⟨⟨h2', hs'⟩, hl'⟩, ⟨h2'', hs''⟩, hc''⟩ := hx
    have h2 : ∀ i, 2 ≤ Fin.append c' c'' i := fun i => by
      induction i using Fin.addCases with
      | left j => simpa using h2' j
      | right j => simpa using h2'' j
    simp only [mem_filter, fpRawSplit_append hk c' c'' hl' fun j => (hc'' j).1,
      wordPrefixSum_append, hs', Int.toNat_natCast, and_true]
    rw [mem_firstPassageWords]
    refine ⟨h2, fun i hi => ?_, ?_, fun i hi h45 => ?_⟩
    · induction i using Fin.addCases with
      | left j => simp at hi; omega
      | right j =>
        rw [Fin.append_right]
        simpa using (hc'' j).2 (by simp at hi; omega)
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, hs', hs'']
      ring
    · induction i using Fin.addCases with
      | left j =>
        rw [sum_Iic_eq_wordPrefixSum]
        refine (wordPrefixSum_mono _ h2 (show (Fin.castAdd k j : ℕ) + 1 ≤ n by simp)).trans ?_
        rw [wordPrefixSum_append, hs']
        exact_mod_cast hm
      | right j =>
        rw [Fin.append_right] at h45
        exact absurd (by simpa using h45) ((hc'' j).1 (by simp at hi; omega))
  · intro c hc
    rw [mem_filter, mem_firstPassageWords] at hc
    obtain ⟨⟨h2, hlast, hsum, -⟩, hf⟩ := hc
    obtain ⟨hn, hm'⟩ := Prod.mk.inj hf
    rw [hn] at hm'
    have hpm : wordPrefixSum c n = m := by
      have := wordPrefixSum_nonneg c h2 n
      omega
    rw [wordPrefixSum_castAdd] at hpm
    rw [Fin.sum_univ_add, hpm] at hsum
    simp only [mem_product, fpRawGreenWords, fpRawHoldWords, mem_filter, mem_rawWords]
    refine ⟨⟨⟨fun i => h2 _, hpm⟩, fun i hi => fpRawSplit_mem c _ (by simp; omega)⟩,
      ⟨fun j => h2 _, by linarith⟩, fun j => ⟨fun hj => fpRawSplit_not_mem c _ (by simp; omega)
        (by simp; omega), fun hj => by simpa using hlast _ (by simp; omega)⟩⟩
  · rintro ⟨c', c''⟩ _
    simp
  · intro c _
    exact Fin.append_castAdd_natAdd
  · rintro ⟨c', c''⟩ _
    simp [varpiWordWeight, Fin.prod_univ_add]

/-- **Raw-word form of the first-passage law.** For `s ∈ ℕ`, `r ≥ 1` and `ℓ ∈ ℤ` with `ℓ > s`,
`F_s(r, ℓ) = ∑_{c ∈ 𝒟_s(r, ℓ)} ∏_{i=1}^r ϖ(c_i)`. -/
@[collatz_pos_dens "lem_rn_fp_raw"]
theorem firstPassageLaw_eq_sum_firstPassageWords (s r : ℕ) (hr : 1 ≤ r) (ℓ : ℤ)
    (hℓ : (s : ℤ) < ℓ) :
    firstPassageLaw s (r, ℓ) = ∑ c ∈ firstPassageWords s r ℓ, ∏ i, varpi (c i) := by
  rw [firstPassageLaw_eq_tsum_sum_holdLaw_mul_green s r ℓ hℓ]
  simp_rw [green_eq_greenClosed]
  rw [tsum_eq_sum (s := range r) fun q hq => sum_eq_zero fun p _ => by
    rw [greenClosed_of_neg (by simp only [mem_range, not_lt] at hq; omega), mul_zero]]
  rw [← sum_range_reflect]
  calc _ = ∑ x ∈ range r ×ˢ range (s + 1), ∑ c ∈ (firstPassageWords s r ℓ).filter
          (fun c => (fpRawSplit c, (wordPrefixSum c (fpRawSplit c)).toNat) = x),
          varpiWordWeight c := by
        rw [sum_product]
        refine sum_congr rfl fun n hn => ?_
        rw [← sum_range_reflect]
        refine sum_congr rfl fun m hm => ?_
        simp only [mem_range] at hn hm
        obtain ⟨k, rfl⟩ : ∃ k, r = n + (k + 1) := ⟨r - n - 1, by omega⟩
        rw [sum_fiber_fpRaw s n (k + 1) (by omega) ℓ m (by omega), mul_comm]
        congr 2 <;> omega
    _ = _ := sum_fiberwise_of_maps_to (fun c hc => ?_) _
  rw [mem_firstPassageWords] at hc
  obtain ⟨h2, -, -, hpre⟩ := hc
  simp only [mem_product, mem_range]
  have hlt := fpRawSplit_lt (by omega) c
  refine ⟨hlt, ?_⟩
  rcases Nat.eq_zero_or_pos (fpRawSplit c) with h0 | hpos
  · rw [h0]
    simp [wordPrefixSum]
  · have h45 := fpRawSplit_mem c ⟨fpRawSplit c - 1, by omega⟩ (by simp; omega)
    have := hpre ⟨fpRawSplit c - 1, by omega⟩ (by simp; omega) (by simpa using h45)
    rw [sum_Iic_eq_wordPrefixSum] at this
    simp only [Nat.sub_add_cancel hpos] at this
    omega

end CollatzPosDens
