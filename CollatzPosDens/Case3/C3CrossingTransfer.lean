/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CrossingSet
public import CollatzPosDens.Case3.C3RawWord
public import CollatzPosDens.Case3.C3SuffixWords
public import CollatzPosDens.StoppingTrace.TrListWeight

/-!
# Raw words of a first raw crossing set

Let `ω ∈ ℕ` and let `c, o, r` be integers with `c ≥ 2`, `1 ≤ o ≤ c` and `r ≥ 1`. The raw word
map `π ↦ raw(π)` identifies the first raw crossing set `𝒞_ω(c, o, r)` with the set of words
`w (c) u`, where `w ∈ ℤ^{r-1}` has letters at least `2` summing to `ω + o - c` and `u ∈ 𝒮_c` is a
suffix word of `c`. Along this identification the list weight factors as
`bw^⊗(π) = (∏ ϖ(wᵢ)) ϖ(c) (∏ ϖ(uᵢ))`, so for every `Ψ` from finite words to `[0, ∞]`
`∑_{π ∈ 𝒞_ω(c,o,r)} bw^⊗(π) Ψ(raw(π)) = ϖ(c) ∑_w ∑_{u ∈ 𝒮_c} (∏ ϖ(wᵢ)) (∏ ϖ(uᵢ)) Ψ(w (c) u)`.

The inverse map cuts a word after each of its letters in `{4, 5}`: a live list whose closing
letters lie in `{4, 5}` has no nonclosing letter in `{4, 5}`, so it is recovered from its raw word.

## Main results

* `CollatzPosDens.tsum_c3CrossingSet_mul_eq`: the transfer identity above.

## Implementation notes

The sums are unconditional sums `∑'` in `ℝ≥0∞`; the real weights `bw^⊗(π)` and `ϖ`, which are
nonnegative, enter through `ENNReal.ofReal`. A word `w ∈ ℤ^{r-1}` is a list of length `r - 1`,
and the double sum over `w` and `u` is an iterated sum over the corresponding subtypes.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-! ### Cutting a word into blocks -/

/-- Prepend a nonclosing letter `a` to the first block of a list of blocks. -/
private def consFirst (a : ℤ) : List (List ℤ × ℤ) → List (List ℤ × ℤ)
  | [] => []
  | b :: π => (a :: b.1, b.2) :: π

/-- Cut a word after each of its letters in `{4, 5}`. -/
private def cutWord : List ℤ → List (List ℤ × ℤ)
  | [] => []
  | a :: z => if a = 4 ∨ a = 5 then ([], a) :: cutWord z else consFirst a (cutWord z)

private lemma cutWord_append_cons {c : List ℤ} {e : ℤ}
    (hc : ∀ x ∈ c, x ∉ ({4, 5} : Set ℤ)) (he : e ∈ ({4, 5} : Set ℤ)) (z : List ℤ) :
    cutWord (c ++ e :: z) = (c, e) :: cutWord z := by
  induction c with
  | nil =>
    have he' : e = 4 ∨ e = 5 := by simpa using he
    simp only [List.nil_append, cutWord, he', ite_true]
  | cons a c ih =>
    have ha : ¬ (a = 4 ∨ a = 5) := by simpa using hc a (by simp)
    simp only [List.cons_append, cutWord, ha, ite_false, ih (fun x hx => hc x (by simp [hx]))]
    rfl

/-- A list of blocks whose closing letters lie in `{4, 5}` and whose nonclosing letters do not is
recovered from its raw word by cutting. -/
private lemma cutWord_c3RawWord {π : List (List ℤ × ℤ)}
    (h1 : ∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) (h2 : ∀ b ∈ π, ∀ x ∈ b.1, x ∉ ({4, 5} : Set ℤ)) :
    cutWord (c3RawWord π) = π := by
  induction π with
  | nil => simp [cutWord]
  | cons b π ih =>
    simp only [List.forall_mem_cons] at h1 h2
    rw [c3RawWord_cons, cutWord_append_cons h2.1 h1.1, ih h1.2 h2.2]

private lemma cutWord_good (z : List ℤ) :
    ∀ b ∈ cutWord z, b.2 ∈ ({4, 5} : Set ℤ) ∧ ∀ x ∈ b.1, x ∉ ({4, 5} : Set ℤ) := by
  induction z with
  | nil => simp [cutWord]
  | cons a z ih =>
    rw [cutWord]
    split_ifs with ha
    · simp only [List.forall_mem_cons]
      exact ⟨⟨by simpa using ha, by simp⟩, ih⟩
    · cases hz : cutWord z with
      | nil => simp [consFirst]
      | cons b π =>
        rw [hz] at ih
        simp only [consFirst, List.forall_mem_cons] at ih ⊢
        refine ⟨⟨ih.1.1, ?_⟩, ih.2⟩
        exact ⟨by simpa using ha, ih.1.2⟩

private lemma c3RawWord_cutWord :
    ∀ z : List ℤ, (∀ h : z ≠ [], z.getLast h ∈ ({4, 5} : Set ℤ)) → c3RawWord (cutWord z) = z
  | [], _ => by simp [cutWord]
  | [a], h => by
    have ha := h (by simp)
    simp only [List.getLast_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    simp [cutWord, ha]
  | a :: b :: z, h => by
    have ih := c3RawWord_cutWord (b :: z) (fun _ => by simpa using h (by simp))
    rw [cutWord]
    split_ifs with ha
    · rw [c3RawWord_cons, ih]
      rfl
    · obtain ⟨b', π, hπ⟩ : ∃ b' π, cutWord (b :: z) = b' :: π := by
        cases hc : cutWord (b :: z) with
        | nil => rw [hc] at ih; simp at ih
        | cons b' π => exact ⟨b', π, rfl⟩
      rw [hπ] at ih ⊢
      simp only [consFirst, c3RawWord_cons] at ih ⊢
      rw [← ih]
      simp

/-! ### Weights and block ends read off the raw word -/

private lemma trListWeight_eq_prod_c3RawWord {π : List (List ℤ × ℤ)}
    (h2 : ∀ b ∈ π, ∀ x ∈ b.1, x ∉ ({4, 5} : Set ℤ)) :
    trListWeight π = ((c3RawWord π).map varpi).prod := by
  induction π with
  | nil => simp
  | cons b π ih =>
    simp only [List.forall_mem_cons] at h2
    obtain ⟨c, e⟩ := b
    rw [trListWeight_cons, ih h2.2, c3RawWord_cons, chBlockWeight_of_forall_notMem e h2.1]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    ring

private lemma varpi_ne_zero_iff (x : ℤ) : varpi x ≠ 0 ↔ 2 ≤ x := by
  refine ⟨two_le_of_varpi_ne_zero, fun hx => ?_⟩
  rw [varpi_of_two_le hx]
  have : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have : (0 : ℝ) < (x : ℝ) - 1 := by linarith
  positivity

private lemma trLive_iff_two_le {π : List (List ℤ × ℤ)}
    (h2 : ∀ b ∈ π, ∀ x ∈ b.1, x ∉ ({4, 5} : Set ℤ)) :
    TrLive π ↔ ∀ x ∈ c3RawWord π, 2 ≤ x := by
  rw [trLive_iff_prod_ne_zero, ← trListWeight_def, trListWeight_eq_prod_c3RawWord h2, ne_eq,
    List.prod_eq_zero_iff]
  simp only [List.mem_map, not_exists, not_and]
  exact forall₂_congr fun x _ => (varpi_ne_zero_iff x)

private lemma length_le_length_c3RawWord (π : List (List ℤ × ℤ)) :
    π.length ≤ (c3RawWord π).length := by
  rw [length_c3RawWord_eq_sum]
  omega

private lemma c3RawWord_ne_nil {π : List (List ℤ × ℤ)} (h : π ≠ []) : c3RawWord π ≠ [] := by
  have := length_le_length_c3RawWord π
  have := List.length_pos_iff.2 h
  exact List.ne_nil_of_length_pos (by omega)

/-- Every partial block point before the last block sits at a closing letter of the raw word
other than the last letter (or is the origin). -/
private lemma chBlockPath_snd_eq_of_lt {π : List (List ℤ × ℤ)}
    (h1 : ∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) {i : ℕ} (hi : i < π.length) :
    (chBlockPath π i).2 = 0 ∨ ∃ p, ∃ hp : p + 1 < (c3RawWord π).length,
      (c3RawWord π)[p] ∈ ({4, 5} : Set ℤ) ∧
        (chBlockPath π i).2 = ((c3RawWord π).take (p + 1)).sum := by
  induction π generalizing i with
  | nil => simp at hi
  | cons b π ih =>
    simp only [List.forall_mem_cons] at h1
    cases i with
    | zero => left; simp
    | succ j =>
      right
      have hj : j < π.length := by simpa using hi
      have hne : π ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hlen := length_le_length_c3RawWord π
      rw [chBlockPath_cons_succ, Prod.snd_add, chBlockPoint_snd]
      simp only [c3RawWord_cons]
      rcases ih h1.2 hj with h0 | ⟨p, hp, hmem, hsum⟩
      · refine ⟨b.1.length, by simp; omega, by simpa using h1.1, ?_⟩
        rw [h0, List.take_length_add_append]
        simp
      · refine ⟨b.1.length + 1 + p, by simp; omega, ?_, ?_⟩
        · rw [List.getElem_append_right (by omega)]
          simpa [show b.1.length + 1 + p - b.1.length = p + 1 by omega] using hmem
        · rw [hsum, show b.1.length + 1 + p + 1 = b.1.length + (p + 1 + 1) by omega,
            List.take_length_add_append]
          simp [add_assoc]

/-- A closing letter of the raw word other than the last sits at the end of a block before the
last block. -/
private lemma exists_chBlockPath_of_mem {π : List (List ℤ × ℤ)}
    (h2 : ∀ b ∈ π, ∀ x ∈ b.1, x ∉ ({4, 5} : Set ℤ)) {p : ℕ}
    (hp : p + 1 < (c3RawWord π).length) (hmem : (c3RawWord π)[p] ∈ ({4, 5} : Set ℤ)) :
    ∃ i < π.length, (chBlockPath π i).2 = ((c3RawWord π).take (p + 1)).sum := by
  induction π generalizing p with
  | nil => simp at hp
  | cons b π ih =>
    simp only [List.forall_mem_cons] at h2
    simp only [c3RawWord_cons, List.length_append, List.length_cons] at hp hmem ⊢
    rcases lt_trichotomy p b.1.length with hlt | rfl | hgt
    · rw [List.getElem_append_left hlt] at hmem
      exact absurd hmem (h2.1 _ (List.getElem_mem hlt))
    · refine ⟨1, ?_, ?_⟩
      · have : π ≠ [] := by
          rintro rfl
          simp at hp
        simpa using List.length_pos_iff.2 this
      · rw [chBlockPath_cons_succ, chBlockPath_zero, Prod.snd_add, chBlockPoint_snd,
          List.take_append, List.take_of_length_le (by simp)]
        simp
    · obtain ⟨p, rfl⟩ : ∃ p', p = b.1.length + 1 + p' := ⟨p - b.1.length - 1, by omega⟩
      rw [List.getElem_append_right (by omega)] at hmem
      simp only [show b.1.length + 1 + p - b.1.length = p + 1 by omega,
        List.getElem_cons_succ] at hmem
      obtain ⟨i, hi, hsum⟩ := ih h2.2 (p := p) (by omega) hmem
      refine ⟨i + 1, by simpa using hi, ?_⟩
      rw [chBlockPath_cons_succ, Prod.snd_add, chBlockPoint_snd, hsum,
        show b.1.length + 1 + p + 1 = b.1.length + (p + 1 + 1) by omega,
        List.take_length_add_append]
      simp [add_assoc]

/-- The last letter of the raw word of a nonempty list is its last closing letter. -/
private lemma getLast_c3RawWord_mem {π : List (List ℤ × ℤ)}
    (h1 : ∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) (h : c3RawWord π ≠ []) :
    (c3RawWord π).getLast h ∈ ({4, 5} : Set ℤ) := by
  obtain ⟨π', b, rfl⟩ := List.eq_nil_or_concat π |>.resolve_left (by rintro rfl; simp at h)
  simp only [List.concat_eq_append, c3RawWord_append, c3RawWord_cons, c3RawWord_nil]
  rw [List.getLast_append_of_ne_nil _ (by simp)]
  simpa using h1 b (by simp)

private lemma sum_take_mono {z : List ℤ} (hz : ∀ x ∈ z, 0 ≤ x) {m n : ℕ} (hmn : m ≤ n) :
    (z.take m).sum ≤ (z.take n).sum := by
  rw [← List.take_append_drop m (z.take n), List.take_take, min_eq_left hmn, List.sum_append]
  refine le_add_of_nonneg_right (List.sum_nonneg fun x hx => hz x ?_)
  exact (List.take_subset _ _) ((List.drop_subset _ _) hx)

/-! ### The transfer identity -/

/-- The suffix words of a nonclosing crossing letter `c ∉ {4, 5}`, characterised letterwise. -/
private lemma mem_c3SuffixWords_iff {c : ℤ} (hc : c ∉ ({4, 5} : Set ℤ)) {u : List ℤ} :
    u ∈ c3SuffixWords c ↔ u ≠ [] ∧ (∀ x ∈ u, 2 ≤ x) ∧
      ∀ i (hi : i < u.length), (u[i] ∈ ({4, 5} : Set ℤ) ↔ i + 1 = u.length) := by
  rw [mem_c3SuffixWords_of_notMem hc]
  constructor
  · rintro ⟨hlen, l, hl⟩
    obtain ⟨h2, hiff, -⟩ := mem_holdWords_iff.1 hl
    refine ⟨List.ne_nil_of_length_pos hlen, fun x hx => ?_, fun i hi => hiff ⟨i, hi⟩⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hx
    exact h2 i
  · rintro ⟨hne, h2, hiff⟩
    exact ⟨List.length_pos_iff.2 hne, _, mem_holdWords_iff.2
      ⟨fun i => h2 _ (List.getElem_mem _), fun i => hiff i i.2, rfl⟩⟩

private lemma trRawSum_eq_sum_take_c3RawWord (π : List (List ℤ × ℤ)) (i : ℕ) :
    trRawSum π i = ((c3RawWord π).take i).sum := by
  rw [trRawSum_eq_sum_take, c3RawWord_eq_flatMap]

private lemma chBlockPath_length_fst (π : List (List ℤ × ℤ)) :
    (chBlockPath π π.length).1 = (c3RawWord π).length := by
  rw [length_c3RawWord, Int.toNat_of_nonneg (chBlockPath_fst_nonneg _ _)]

private lemma chBlockPath_length_snd (π : List (List ℤ × ℤ)) :
    (chBlockPath π π.length).2 = (c3RawWord π).sum := by
  rw [c3RawWord_eq_flatMap, sum_flatMap_eq_chBlockPath_snd]

/-- From lists to words: the raw word of `π ∈ 𝒞_ω(c, o, r)` is `w (c) u` with `w` a word of
length `r - 1` of letters at least `2` summing to `ω + o - c` and `u ∈ 𝒮_c`. -/
private lemma c3RawWord_of_mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ} (ho : 1 ≤ o)
    (hr : 1 ≤ r) {π : List (List ℤ × ℤ)} (h : π ∈ c3CrossingSet ω c o r) :
    ((∀ b ∈ π, b.2 ∈ ({4, 5} : Set ℤ)) ∧ ∀ b ∈ π, ∀ x ∈ b.1, x ∉ ({4, 5} : Set ℤ)) ∧
      (((c3RawWord π).take (r - 1)).length = r - 1 ∧
        (∀ x ∈ (c3RawWord π).take (r - 1), 2 ≤ x) ∧
        ((c3RawWord π).take (r - 1)).sum = ω + o - c) ∧
      (c3RawWord π).drop r ∈ c3SuffixWords c ∧
      c3RawWord π = (c3RawWord π).take (r - 1) ++ c :: (c3RawWord π).drop r := by
  obtain ⟨hπ, hrM, hσ₁, hσ₂⟩ := h
  have h1 := hπ.1
  have h2 : ∀ b ∈ π, ∀ x ∈ b.1, x ∉ ({4, 5} : Set ℤ) := fun b hb x hx hx45 =>
    hπ.2.1 b hb (chBlockWeight_eq_zero_of_mem hx hx45)
  rw [chBlockPath_length_fst] at hrM
  rw [trRawSum_eq_sum_take_c3RawWord] at hσ₁ hσ₂
  set z := c3RawWord π with hz
  have hz2 : ∀ x ∈ c3RawWord π, 2 ≤ x := (trLive_iff_two_le h2).1 hπ.2.1
  have hexists := fun p => exists_chBlockPath_of_mem h2 (p := p)
  have hne : c3RawWord π ≠ [] := c3RawWord_ne_nil (ne_nil_of_mem_trPassage hπ)
  have hlast : z[z.length - 1]'(by simpa [Nat.pos_iff_ne_zero] using hne) ∈
      ({4, 5} : Set ℤ) := by
    simpa [List.getLast_eq_getElem] using getLast_c3RawWord_mem h1 hne
  have hz0 : ∀ x ∈ z, 0 ≤ x := fun x hx => by linarith [hz2 x hx]
  have hrz : r ≤ z.length := by exact_mod_cast hrM
  have hlt : r - 1 < z.length := by omega
  have hzc : z[r - 1] = c := by
    have := List.sum_take_succ z (r - 1) hlt
    rw [Nat.sub_add_cancel hr, hσ₁, hσ₂] at this
    linarith
  have hpos : ∀ p (hp : p + 1 < z.length), z[p] ∈ ({4, 5} : Set ℤ) → p + 1 < r := by
    intro p hp hmem
    by_contra hge
    obtain ⟨i, hi, hsum⟩ := hexists p hp hmem
    have h3 := chBlockPath_snd_le_of_mem_trPassage hπ hi
    have h4 := sum_take_mono hz0 (not_lt.1 hge)
    linarith
  refine ⟨⟨h1, h2⟩, ⟨by simp; omega, fun x hx => hz2 x (List.take_subset _ _ hx), hσ₁⟩, ?_, ?_⟩
  · by_cases hc : c ∈ ({4, 5} : Set ℤ)
    · rw [mem_c3SuffixWords_of_mem hc, List.drop_eq_nil_iff]
      by_contra hlen
      have := hpos (r - 1) (by omega) (hzc ▸ hc)
      omega
    · rw [mem_c3SuffixWords_iff hc]
      refine ⟨?_, fun x hx => hz2 x (List.drop_subset _ _ hx), fun i hi => ?_⟩
      · intro hd
        rw [List.drop_eq_nil_iff] at hd
        have : z.length - 1 = r - 1 := by omega
        simp only [this, hzc] at hlast
        exact hc hlast
      · rw [List.getElem_drop]
        simp only [List.length_drop] at hi ⊢
        constructor
        · intro hmem
          by_contra hne'
          have := hpos (r + i) (by omega) hmem
          omega
        · intro hi'
          have : r + i = z.length - 1 := by omega
          simp only [this]
          exact hlast
  · conv_lhs => rw [← List.take_append_drop (r - 1) z, List.drop_eq_getElem_cons hlt, hzc,
      Nat.sub_add_cancel hr]

/-- From words to lists: for `w` of length `r - 1` with letters at least `2` summing to
`ω + o - c` and `u ∈ 𝒮_c`, cutting `w (c) u` gives a list of `𝒞_ω(c, o, r)` with raw word
`w (c) u`. -/
private lemma cutWord_mem_c3CrossingSet {ω : ℕ} {c o : ℤ} {r : ℕ} (hc2 : 2 ≤ c) (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) {w u : List ℤ} (hwl : w.length = r - 1) (hw2 : ∀ x ∈ w, 2 ≤ x)
    (hws : w.sum = ω + o - c) (hu : u ∈ c3SuffixWords c) :
    cutWord (w ++ c :: u) ∈ c3CrossingSet ω c o r ∧
      c3RawWord (cutWord (w ++ c :: u)) = w ++ c :: u := by
  set z := w ++ c :: u with hz
  have hu2 := two_le_of_mem_c3SuffixWords hu
  have hz2 : ∀ x ∈ z, 2 ≤ x := by
    intro x hx
    simp only [hz, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    exacts [hw2 x hx, hc2, hu2 x hx]
  have hz0 : ∀ x ∈ z, 0 ≤ x := fun x hx => by linarith [hz2 x hx]
  have hzr : z.length = r + u.length := by simp [hz]; omega
  have hzc : ∀ (h : r - 1 < z.length), z[r - 1] = c := by
    intro h
    simp only [hz, List.getElem_append_right (show w.length ≤ r - 1 by omega), hwl,
      Nat.sub_self, List.getElem_cons_zero]
  have hzu : ∀ i (h : r + i < z.length), z[r + i] = u[i]'(by omega) := by
    intro i h
    simp only [hz, List.getElem_append_right (show w.length ≤ r + i by omega), hwl,
      show r + i - (r - 1) = i + 1 by omega, List.getElem_cons_succ]
  have hpos : ∀ p (hp : p + 1 < z.length), z[p] ∈ ({4, 5} : Set ℤ) → p + 1 < r := by
    intro p hp hmem
    by_contra hge
    by_cases hc : c ∈ ({4, 5} : Set ℤ)
    · rw [mem_c3SuffixWords_of_mem hc] at hu
      simp [hu] at hzr
      omega
    · obtain ⟨-, -, hiff⟩ := (mem_c3SuffixWords_iff hc).1 hu
      rcases (show p = r - 1 ∨ r ≤ p by omega) with rfl | hp'
      · exact hc (by simpa [hzc (by omega)] using hmem)
      · obtain ⟨i, rfl⟩ : ∃ i, p = r + i := ⟨p - r, by omega⟩
        rw [hzu i (by omega)] at hmem
        have := (hiff i (by omega)).1 hmem
        omega
  have hlast : ∀ h : z ≠ [], z.getLast h ∈ ({4, 5} : Set ℤ) := by
    intro h
    rw [List.getLast_eq_getElem]
    by_cases hc : c ∈ ({4, 5} : Set ℤ)
    · rw [mem_c3SuffixWords_of_mem hc] at hu
      simp only [hu, List.length_nil, add_zero] at hzr
      have e : z.length - 1 = r - 1 := by omega
      simpa [e, hzc (by omega)] using hc
    · obtain ⟨hne, -, hiff⟩ := (mem_c3SuffixWords_iff hc).1 hu
      have hul := List.length_pos_iff.2 hne
      have e : z.length - 1 = r + (u.length - 1) := by omega
      simp only [e, hzu (u.length - 1) (by omega)]
      exact (hiff _ (by omega)).2 (by omega)
  have hraw := c3RawWord_cutWord z hlast
  set π := cutWord z with hπdef
  obtain ⟨h1, h2⟩ := forall_and.1 fun b => forall_and.1 fun (hb : b ∈ π) => cutWord_good z b hb
  refine ⟨⟨⟨h1, (trLive_iff_two_le (fun b hb => h2 b hb)).2 (hraw ▸ hz2), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
    hraw⟩
  · rintro hnil
    rw [hnil, c3RawWord_nil] at hraw
    simp [hz] at hraw
  · intro i hi
    rcases chBlockPath_snd_eq_of_lt (fun b hb => h1 b hb) hi with h0 | ⟨p, hp, hmem, hsum⟩
    · rw [h0]
      positivity
    · rw [hsum]
      simp only [hraw] at hp hmem ⊢
      have := hpos p hp hmem
      have h3 := sum_take_mono hz0 (show p + 1 ≤ r - 1 by omega)
      have h4 : z.take (r - 1) = w := by rw [hz, List.take_left' hwl]
      rw [h4, hws] at h3
      omega
  · rw [chBlockPath_length_snd, hraw]
    have : 0 ≤ u.sum := List.sum_nonneg fun x hx => by linarith [hu2 x hx]
    simp only [hz, List.sum_append, List.sum_cons]
    omega
  · rw [chBlockPath_length_fst, hraw]
    exact_mod_cast (show r ≤ z.length by omega)
  · rw [trRawSum_eq_sum_take_c3RawWord, hraw, hz, List.take_left' hwl]
    exact hws
  · rw [trRawSum_eq_sum_take_c3RawWord, hraw, hz, show r = w.length + 1 by omega,
      List.take_length_add_append]
    simp [hws]

private lemma prod_map_varpi_nonneg (w : List ℤ) :
    0 ≤ (w.map varpi).prod :=
  List.prod_nonneg fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact varpi_nonneg y

/-- **Raw words of a first raw crossing set.** Let `ω ∈ ℕ`, let `c, o, r` be integers with
`c ≥ 2`, `1 ≤ o ≤ c` and `r ≥ 1`, and let `Ψ` be a function from the finite words of integers to
`[0, ∞]`. Then
`∑_{π ∈ 𝒞_ω(c,o,r)} bw^⊗(π) Ψ(raw(π)) = ϖ(c) ∑_w ∑_{u ∈ 𝒮_c} (∏ᵢ ϖ(wᵢ)) (∏ᵢ ϖ(uᵢ)) Ψ(w (c) u)`,
the sum over `w` ranging over the words `w ∈ ℤ^{r-1}` with `wᵢ ≥ 2` for all `i` and
`w₁ + ⋯ + w_{r-1} = ω + o - c`. -/
@[collatz_pos_dens "lem_c3_crossing_transfer"]
theorem tsum_c3CrossingSet_mul_eq (ω : ℕ) {c o : ℤ} {r : ℕ} (hc : 2 ≤ c) (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) (Ψ : List ℤ → ℝ≥0∞) :
    ∑' π : c3CrossingSet ω c o r, ENNReal.ofReal (trListWeight π.1) * Ψ (c3RawWord π.1) =
      ENNReal.ofReal (varpi c) *
        ∑' w : {w : List ℤ // w.length = r - 1 ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = ω + o - c},
          ∑' u : c3SuffixWords c, ENNReal.ofReal (w.1.map varpi).prod *
            ENNReal.ofReal (u.1.map varpi).prod * Ψ (w.1 ++ c :: u.1) := by
  let W := {w : List ℤ // w.length = r - 1 ∧ (∀ x ∈ w, 2 ≤ x) ∧ w.sum = ω + o - c}
  let F : c3CrossingSet ω c o r → W × c3SuffixWords c := fun π =>
    (⟨(c3RawWord π.1).take (r - 1), (c3RawWord_of_mem_c3CrossingSet ho hr π.2).2.1⟩,
      ⟨(c3RawWord π.1).drop r, (c3RawWord_of_mem_c3CrossingSet ho hr π.2).2.2.1⟩)
  let G : W × c3SuffixWords c → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (varpi c) * (ENNReal.ofReal (p.1.1.map varpi).prod *
      ENNReal.ofReal (p.2.1.map varpi).prod * Ψ (p.1.1 ++ c :: p.2.1))
  have hG : ∀ π, ENNReal.ofReal (trListWeight π.1) * Ψ (c3RawWord π.1) = G (F π) := by
    intro π
    obtain ⟨⟨-, h2⟩, -, -, hdec⟩ := c3RawWord_of_mem_c3CrossingSet ho hr π.2
    simp only [G, F]
    rw [trListWeight_eq_prod_c3RawWord h2]
    conv_lhs => rw [hdec]
    simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    rw [ENNReal.ofReal_mul (prod_map_varpi_nonneg _), ENNReal.ofReal_mul (varpi_nonneg c)]
    ring
  have hF : Function.Bijective F := by
    refine ⟨fun π π' h => ?_, fun ⟨w, u⟩ => ?_⟩
    · simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, -, -, hdec⟩ := c3RawWord_of_mem_c3CrossingSet ho hr π.2
      obtain ⟨⟨h1', h2'⟩, -, -, hdec'⟩ := c3RawWord_of_mem_c3CrossingSet ho hr π'.2
      have e1 := congrArg Subtype.val h.1
      have hraw : c3RawWord π.1 = c3RawWord π'.1 := by
        rw [hdec, hdec']
        simp only at e1
        rw [e1, h.2]
      apply Subtype.ext
      rw [← cutWord_c3RawWord h1 h2, ← cutWord_c3RawWord h1' h2', hraw]
    · obtain ⟨hmem, hraw⟩ := cutWord_mem_c3CrossingSet hc ho hoc hr w.2.1 w.2.2.1 w.2.2.2 u.2
      refine ⟨⟨_, hmem⟩, ?_⟩
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change List.take (r - 1) (c3RawWord (cutWord (w.1 ++ c :: u.1))) = w.1
        rw [hraw]
        exact List.take_left' w.2.1
      · change List.drop r (c3RawWord (cutWord (w.1 ++ c :: u.1))) = u.1
        rw [hraw]
        have key : ∀ n, n = w.1.length + 1 → List.drop n (w.1 ++ c :: u.1) = u.1 := by
          rintro _ rfl
          simp
        exact key r (by have := w.2.1; omega)
  calc ∑' π : c3CrossingSet ω c o r, ENNReal.ofReal (trListWeight π.1) * Ψ (c3RawWord π.1)
      = ∑' π, G (F π) := tsum_congr hG
    _ = ∑' p, G p := (Equiv.ofBijective F hF).tsum_eq G
    _ = ∑' w : W, ∑' u : c3SuffixWords c, G (w, u) :=
      ENNReal.tsum_prod (f := fun w u => G (w, u))
    _ = _ := by
      simp only [G, ENNReal.tsum_mul_left]
      rfl

end CollatzPosDens
