/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrRaw3LastBlock
public import CollatzPosDens.StoppingTrace.TrRaw3Witness
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# Mass of the first raw crossing events

For `s ∈ ℕ` and integers `c, o, r` with `1 ≤ o ≤ c` and `r ≥ 1`, the first raw crossing events
`𝒳_{c,o,r}(s)` carry total weight `ϖ(c) 𝖱(r - 1, s + o - c)`:
`∑_{π ∈ 𝒳_{c,o,r}(s)} bw^⊗(π) = ϖ(c) 𝖱(r - 1, s + o - c)`.

The raw word `z = c¹ (e¹) ⋯ cᵏ (eᵏ)` of a live list `π` has letters `≥ 2`, its letters in
`{4, 5}` are exactly the closing letters, and `bw^⊗(π) = ∏ ϖ(zᵢ)`; conversely a word whose last
letter lies in `{4, 5}` is the raw word of exactly one list, obtained by cutting it after each
of its letters in `{4, 5}`. A list `π ∈ 𝒳_{c,o,r}(s)` has, by `trRawThreeWitness_lastBlock`, its
`r`-th letter `c` in the last block, so its raw word is `b (c) y`, where `b` has length `r - 1`,
letters `≥ 2` and sum `s + o - c`, and `y` is the rest of the last block. Conversely, cutting
such a word gives a list of `𝒳_{c,o,r}(s)` as soon as its weight is nonzero: the block endpoints
before the last lie inside `b`, at height at most `s + o - c ≤ s`, and the last one is at height
at least `s + o > s`.

If `c ∈ {4, 5}`, the letter `c` closes the last block and `y` is empty, so the total weight is
`ϖ(c) 𝖱(r - 1, s + o - c)`. Otherwise `c (y)` is a block `(c c', e)` with `(c', e)` an arbitrary
block, of weight `ϖ(c) bw(c', e)`, and the block weights have total mass `1`.

## Main results

* `CollatzPosDens.hasSum_trListWeight_trRawThreeWitness`: the series
  `∑_{π ∈ 𝒳_{c,o,r}(s)} bw^⊗(π)` converges (unconditionally) to `ϖ(c) 𝖱(r - 1, s + o - c)`.
* `CollatzPosDens.tsum_trListWeight_trRawThreeWitness`: the same identity for `tsum`.

## Implementation notes

The sum over `𝒳_{c,o,r}(s)` is stated as a `HasSum` over the subtype `trRawThreeWitness s c o r`;
this records the convergence of the series as well as its value, and since the terms are
nonnegative it is the strongest form of the statement. The hypothesis `c ≥ 2` is not
needed: for `c < 2` both sides vanish, as every letter of a live list is at least `2` and
`ϖ(c) = 0`.

When `c ∉ {4, 5}`, the remaining letters are not summed as the geometric series
`∑_{m ≥ 0} (∑_{a ∉ {4, 5}} ϖ(a))^m (ϖ(4) + ϖ(5))`; instead the words carry the whole remaining
block `(c', e)` and its weight `bw(c', e)`, which already vanishes when a letter of `c'` lies in
`{4, 5}`, and the factor is the total block mass `hasSum_prod_chBlockWeight_single`. The words
whose list has weight zero are kept: they do not contribute, and keeping them makes the
word-to-list map injective on all words, which is what `Function.Injective.hasSum_iff` needs.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/


@[expose] public section

namespace CollatzPosDens

open Finset

/-! ### Cutting a word into blocks -/

/-- Cut the word `acc ++ w` after each of the letters of `w` lying in `{4, 5}`: the blocks so
obtained, and the remaining word after the last such letter. -/
private def cutBlocks : List ℤ → List ℤ → List (List ℤ × ℤ) × List ℤ
  | acc, [] => ([], acc)
  | acc, a :: w =>
    if a = 4 ∨ a = 5 then ((acc, a) :: (cutBlocks [] w).1, (cutBlocks [] w).2)
    else cutBlocks (acc ++ [a]) w

private lemma cutBlocks_flat (acc w : List ℤ) :
    ((cutBlocks acc w).1.flatMap fun b => b.1 ++ [b.2]) ++ (cutBlocks acc w).2 = acc ++ w := by
  induction w generalizing acc with
  | nil => simp [cutBlocks]
  | cons a w ih =>
    by_cases ha : a = 4 ∨ a = 5
    · simp only [cutBlocks, ha, ↓reduceIte, List.flatMap_cons, List.append_assoc]
      rw [ih]; simp
    · simp only [cutBlocks, ha, ↓reduceIte]
      rw [ih]; simp

private lemma cutBlocks_closing (acc w : List ℤ) :
    ∀ b ∈ (cutBlocks acc w).1, b.2 ∈ ({4, 5} : Set ℤ) := by
  induction w generalizing acc with
  | nil => simp [cutBlocks]
  | cons a w ih =>
    by_cases ha : a = 4 ∨ a = 5
    · simp only [cutBlocks, ha, ↓reduceIte, List.mem_cons, forall_eq_or_imp]
      exact ⟨by simpa using ha, ih []⟩
    · simp only [cutBlocks, ha, ↓reduceIte]
      exact ih _

private lemma cutBlocks_weight (acc w : List ℤ) :
    trListWeight (cutBlocks acc w).1 * ((cutBlocks acc w).2.map varpiIn).prod =
      (acc.map varpiIn).prod * (w.map varpi).prod := by
  induction w generalizing acc with
  | nil => simp [cutBlocks]
  | cons a w ih =>
    by_cases ha : a = 4 ∨ a = 5
    · simp only [cutBlocks, ha, ↓reduceIte, trListWeight_cons, chBlockWeight_mk]
      have := ih []
      simp only [List.map_nil, List.prod_nil, one_mul] at this
      rw [mul_assoc, this]
      simp only [List.map_cons, List.prod_cons]
      ring
    · simp only [cutBlocks, ha, ↓reduceIte]
      rw [ih]
      simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons,
        List.map_nil, List.prod_nil, varpiIn_of_notMem ha]
      ring

private lemma cutBlocks_of_forall (acc u : List ℤ) (hu : ∀ x ∈ u, ¬ (x = 4 ∨ x = 5)) :
    cutBlocks acc u = ([], acc ++ u) := by
  induction u generalizing acc with
  | nil => simp [cutBlocks]
  | cons a u ih =>
    have ha := hu a (by simp)
    simp only [cutBlocks, ha, ↓reduceIte]
    rw [ih _ fun x hx ↦ hu x (by simp [hx])]
    simp

private lemma cutBlocks_block (acc c w : List ℤ) (e : ℤ) (hc : ∀ x ∈ c, ¬ (x = 4 ∨ x = 5))
    (he : e = 4 ∨ e = 5) :
    cutBlocks acc (c ++ e :: w) = ((acc ++ c, e) :: (cutBlocks [] w).1, (cutBlocks [] w).2) := by
  induction c generalizing acc with
  | nil => simp [cutBlocks, he]
  | cons a c ih =>
    have ha := hc a (by simp)
    simp only [List.cons_append, cutBlocks, ha, ↓reduceIte]
    rw [ih _ fun x hx ↦ hc x (by simp [hx])]
    simp

private lemma cutBlocks_flat_append (β : List (List ℤ × ℤ)) (u : List ℤ)
    (hβ : ∀ b ∈ β, (∀ x ∈ b.1, ¬ (x = 4 ∨ x = 5)) ∧ (b.2 = 4 ∨ b.2 = 5))
    (hu : ∀ x ∈ u, ¬ (x = 4 ∨ x = 5)) :
    cutBlocks [] ((β.flatMap fun b => b.1 ++ [b.2]) ++ u) = (β, u) := by
  induction β with
  | nil => simpa using cutBlocks_of_forall [] u hu
  | cons b β ih =>
    obtain ⟨hb1, hb2⟩ := hβ b (by simp)
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append]
    rw [cutBlocks_block _ _ _ _ hb1 hb2]
    simp only [List.nil_append]
    rw [ih fun b' hb' ↦ hβ b' (by simp [hb'])]


/-! ### The list with a given raw word -/

/-- The list of blocks with raw word `b c (e)`: the word `b` cut after its letters in `{4, 5}`,
followed by the block whose nonclosing word is the rest of `b` followed by `c`. -/
private def buildList (b c : List ℤ) (e : ℤ) : List (List ℤ × ℤ) :=
  (cutBlocks [] b).1 ++ [((cutBlocks [] b).2 ++ c, e)]

private lemma buildList_flat (b c : List ℤ) (e : ℤ) :
    ((buildList b c e).flatMap fun β => β.1 ++ [β.2]) = b ++ (c ++ [e]) := by
  have h := cutBlocks_flat [] b
  rw [List.nil_append] at h
  conv_rhs => rw [← h]
  simp [buildList]

private lemma buildList_weight (b c : List ℤ) (e : ℤ) :
    trListWeight (buildList b c e) = (b.map varpi).prod * chBlockWeight (c, e) := by
  have h := cutBlocks_weight [] b
  simp only [List.map_nil, List.prod_nil, one_mul] at h
  rw [buildList, trListWeight_concat, chBlockWeight_append]
  linear_combination chBlockWeight (c, e) * h

private lemma buildList_closing {b c : List ℤ} {e : ℤ} (he : e ∈ ({4, 5} : Set ℤ)) :
    ∀ x ∈ buildList b c e, x.2 ∈ ({4, 5} : Set ℤ) := by
  intro x hx
  simp only [buildList, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact cutBlocks_closing [] b x hx
  · exact he

private lemma sum_map_eq_sum_flat (β : List (List ℤ × ℤ)) :
    (β.map fun b => b.1.sum + b.2).sum = (β.flatMap fun b => b.1 ++ [b.2]).sum := by
  induction β with
  | nil => simp
  | cons b β ih => simp [ih, add_assoc]

/-- The list with raw word `b (a) t` is a first raw crossing event of `𝒳_{a,o,|b|+1}(s)` as soon
as its weight is nonzero, `0 < o ≤ a` and `∑ b = s + o - a`. -/
private lemma buildList_mem {s : ℕ} {a o : ℤ} {b c t : List ℤ} {e : ℤ}
    (hbs : b.sum = s + o - a) (ho : 0 < o) (hoa : o ≤ a) (hct : c ++ [e] = a :: t)
    (he : e ∈ ({4, 5} : Set ℤ)) (hw : trListWeight (buildList b c e) ≠ 0) :
    buildList b c e ∈ trRawThreeWitness s a o (b.length + 1) := by
  have hlive : TrLive (buildList b c e) := (trLive_iff_prod_ne_zero _).mpr hw
  have hflat : ((buildList b c e).flatMap fun β => β.1 ++ [β.2]) = b ++ a :: t := by
    rw [buildList_flat, hct]
  have hlet : ∀ x ∈ b ++ a :: t, 2 ≤ x := by
    intro x hx
    rw [← hflat] at hx
    obtain ⟨β, hβ, hxβ⟩ := List.mem_flatMap.mp hx
    exact two_le_of_mem_append_of_chBlockWeight_ne_zero (hlive β hβ) hxβ
  have hb : ∀ x ∈ b, 0 ≤ x := fun x hx ↦ by linarith [hlet x (by simp [hx])]
  have ht : 0 ≤ t.sum := List.sum_nonneg fun x hx ↦ by linarith [hlet x (by simp [hx])]
  refine ⟨⟨buildList_closing he, hlive, by simp [buildList], ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi
    have hlen : (buildList b c e).length = (cutBlocks [] b).1.length + 1 := by simp [buildList]
    rw [hlen] at hi
    rw [chBlockPath_snd, buildList, List.take_append_of_le_length (by omega),
      sum_map_eq_sum_flat]
    refine (List.IsPrefix.sublist ?_ |>.sum_le_sum hb).trans (by omega)
    have h1 : ((cutBlocks [] b).1.take i).flatMap (fun b => b.1 ++ [b.2]) <+:
        (cutBlocks [] b).1.flatMap (fun b => b.1 ++ [b.2]) := by
      conv_rhs => rw [← List.take_append_drop i (cutBlocks [] b).1]
      rw [List.flatMap_append]
      exact List.prefix_append _ _
    refine h1.trans ?_
    have h := cutBlocks_flat [] b
    rw [List.nil_append] at h
    conv_rhs => rw [← h]
    exact List.prefix_append _ _
  · rw [← sum_flatMap_eq_chBlockPath_snd, hflat]
    simp only [List.sum_append, List.sum_cons]
    omega
  · rw [toNat_chBlockPath_fst, hflat]
    simp
  · rw [chRaw_toNat_chBlockPath_fst, hflat]
    simp
  · rw [trRawSum_eq_sum_take, hflat, List.take_append, List.take_of_length_le (by omega)]
    simp only [Nat.add_sub_cancel_left, List.take_succ_cons, List.take_zero, List.sum_append,
      List.sum_cons, List.sum_nil]
    omega

/-- Every first raw crossing event `π ∈ 𝒳_{a,o,r}(s)` with `0 < o` is the list with raw word
`b c (e)`, where `b` has length `r - 1`, letters `≥ 2` and sum `s + o - a`, the word `c (e)`
starts with the letter `a`, the letters of `c` lie outside `{4, 5}` and `e ∈ {4, 5}`. -/
private lemma exists_buildList {s : ℕ} {a o : ℤ} {r : ℕ} (ho : 0 < o)
    {π : List (List ℤ × ℤ)} (hπ : π ∈ trRawThreeWitness s a o r) :
    ∃ b c e t, b.length = r - 1 ∧ (∀ x ∈ b, 2 ≤ x) ∧ b.sum = s + o - a ∧
      c ++ [e] = a :: t ∧ (∀ x ∈ c, x ∉ ({4, 5} : Set ℤ)) ∧ e ∈ ({4, 5} : Set ℤ) ∧
      π = buildList b c e := by
  have hP := trRawThreeWitness_mem_trPassage hπ
  have hlive := trLive_of_mem_trPassage hP
  obtain ⟨π₀, ⟨d, e⟩, rfl⟩ : ∃ π₀ x, π = π₀ ++ [x] :=
    ⟨_, _, (List.dropLast_append_getLast (ne_nil_of_mem_trPassage hP)).symm⟩
  obtain ⟨i, hi1, hid, hci, hpt⟩ :=
    trRawThreeWitness_lastBlock ho hπ (d := d) (e := e) (by simp)
  have hlastw : chBlockWeight (d, e) ≠ 0 := hlive _ (by simp)
  have he : e ∈ ({4, 5} : Set ℤ) := trRawThreeWitness_closing_mem hπ (b := (d, e)) (by simp)
  have hd : ∀ x ∈ d, x ∉ ({4, 5} : Set ℤ) := fun x hx h ↦
    hlastw (chBlockWeight_eq_zero_of_mem hx h)
  have hπ₀ : ∀ β ∈ π₀, (∀ x ∈ β.1, ¬ (x = 4 ∨ x = 5)) ∧ (β.2 = 4 ∨ β.2 = 5) := by
    intro β hβ
    refine ⟨fun x hx h ↦
      hlive β (by simp [hβ]) (chBlockWeight_eq_zero_of_mem hx (by simpa using h)), ?_⟩
    simpa using trRawThreeWitness_closing_mem hπ (b := β) (by simp [hβ])
  have hlen : (π₀ ++ [(d, e)]).length - 1 = π₀.length := by simp
  rw [hlen, chBlockPath_append_of_le _ _ le_rfl] at hpt
  set z₀ := π₀.flatMap fun β => β.1 ++ [β.2] with hz₀
  have hfst : (chBlockPath π₀ π₀.length).1 = (z₀.length : ℤ) := by
    rw [← toNat_chBlockPath_fst, Int.toNat_of_nonneg (chBlockPath_fst_nonneg _ _)]
  have hsnd : (chBlockPath π₀ π₀.length).2 = z₀.sum := (sum_flatMap_eq_chBlockPath_snd π₀).symm
  have hr := congrArg Prod.fst hpt
  have hσ := congrArg Prod.snd hpt
  simp only [Prod.fst_add, Prod.snd_add, hfst, hsnd] at hr hσ
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hci
  have htake : (d ++ [e]).take (j + 1) = d.take j ++ [a] := by
    rw [List.take_add_one, hci, List.take_append_of_le_length (by omega)]
    rfl
  rw [htake, List.sum_append, List.sum_singleton] at hσ
  have hdrop : d.drop j ++ [e] = a :: (d ++ [e]).drop (j + 1) := by
    rw [← List.drop_append_of_le_length (by omega), List.drop_eq_getElem_cons]
    · obtain ⟨_, h⟩ := List.getElem?_eq_some_iff.mp hci
      rw [h]
    · simp only [List.length_append, List.length_singleton]
      omega
  refine ⟨z₀ ++ d.take j, d.drop j, e, (d ++ [e]).drop (j + 1), ?_, ?_, ?_, hdrop,
    fun x hx ↦ hd x (List.mem_of_mem_drop hx), he, ?_⟩
  · simp only [List.length_append, List.length_take]
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨β, hβ, hxβ⟩ := List.mem_flatMap.mp hx
      exact two_le_of_mem_append_of_chBlockWeight_ne_zero (hlive β (by simp [hβ])) hxβ
    · exact two_le_of_chBlockWeight_ne_zero hlastw (List.mem_of_mem_take hx)
  · rw [List.sum_append]
    omega
  · rw [buildList, cutBlocks_flat_append π₀ (d.take j) hπ₀
      fun x hx h ↦ hd x (List.mem_of_mem_take hx) (by simpa using h), List.take_append_drop]

/-- A word of length `n` is `List.ofFn` of a tuple in `ℤⁿ`. -/
private lemma exists_ofFn_eq {n : ℕ} {b : List ℤ} (hb : b.length = n) :
    ∃ f : Fin n → ℤ, List.ofFn f = b := by
  subst hb
  exact ⟨b.get, List.ofFn_get b⟩

/-- A word `b` of length `r - 1`, with letters `≥ 2` and sum `t`, is `List.ofFn` of an element
of `rawWords (r - 1) t`. -/
private lemma exists_rawWords {r : ℕ} {t : ℤ} {b : List ℤ} (hb : b.length = r - 1)
    (h2 : ∀ x ∈ b, 2 ≤ x) (hs : b.sum = t) :
    ∃ f : rawWords (r - 1) t, List.ofFn f.1 = b := by
  obtain ⟨f, rfl⟩ := exists_ofFn_eq hb
  refine ⟨⟨f, mem_rawWords.mpr ⟨fun i ↦ h2 _ (List.mem_ofFn.mpr ⟨i, rfl⟩), ?_⟩⟩, rfl⟩
  rwa [← List.sum_ofFn]

/-- The weight of a word `f`, as a list. -/
private lemma prod_map_varpi_ofFn {n : ℕ} (f : Fin n → ℤ) :
    ((List.ofFn f).map varpi).prod = ∏ i, varpi (f i) := by
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/-! ### Parametrising the first raw crossing events -/

/-- If `f : ι → List (List ℤ × ℤ)` is injective with range containing `W`, and the weight of
`f x` restricted to `W` is `g x`, then `∑_{π ∈ W} bw^⊗(π)` has the sum of `g`. -/
private lemma hasSum_of_parametrisation {ι : Type*} {W : Set (List (List ℤ × ℤ))}
    (f : ι → List (List ℤ × ℤ)) (hf : Function.Injective f) (hW : ∀ π ∈ W, π ∈ Set.range f)
    {g : ι → ℝ} (hg : ∀ x, W.indicator trListWeight (f x) = g x) {m : ℝ} (h : HasSum g m) :
    HasSum (fun π : W ↦ trListWeight π.1) m := by
  rw [show (fun π : W ↦ trListWeight π.1) = trListWeight ∘ Subtype.val from rfl,
    hasSum_subtype_iff_indicator, ← hf.hasSum_iff
    fun π hπ ↦ Set.indicator_of_notMem (fun hA ↦ hπ (hW π hA)) _]
  convert h using 1
  exact funext hg

/-- The weight of a list `π`, restricted to a set `W` containing `π` whenever its weight is
nonzero, is the weight of `π`. -/
private lemma indicator_trListWeight_eq {W : Set (List (List ℤ × ℤ))} {π : List (List ℤ × ℤ)}
    (h : trListWeight π ≠ 0 → π ∈ W) : W.indicator trListWeight π = trListWeight π := by
  rw [Set.indicator_apply_eq_self]
  intro hπ
  by_contra hw
  exact hπ (h hw)

/-- The blocks `(c, e)` with closing letter `e ∈ {4, 5}`. -/
private abbrev ClosingBlock := {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}

/-- Summing `u(b) v bw(β)` over the pairs of an element `b` of a finite set `W` and a block `β`
gives `v ∑_{b ∈ W} u(b)`, since the block weights have total mass `1`. -/
private lemma hasSum_finset_mul_chBlockWeight {α : Type*} (W : Finset α) (u : α → ℝ)
    (hu : ∀ a, 0 ≤ u a) {v : ℝ} (hv : 0 ≤ v) :
    HasSum (fun x : W × ClosingBlock ↦ u x.1 * v * chBlockWeight x.2.1)
      (v * ∑ a ∈ W, u a) := by
  have h1 : HasSum (fun a : W ↦ u a * v) (∑ a : W, u a * v) := hasSum_fintype _
  have h2 := hasSum_prod_chBlockWeight_single
  have h := h1.mul h2 (Summable.mul_of_nonneg h1.summable h2.summable
    (fun a ↦ mul_nonneg (hu _) hv) (fun β ↦ chBlockWeight_nonneg _))
  rwa [mul_one, Finset.sum_coe_sort W (fun a ↦ u a * v), ← Finset.sum_mul, mul_comm] at h

private lemma ofFn_eq_of_buildList_eq {n : ℕ} {f f' : Fin n → ℤ} {c c' : List ℤ} {e e' : ℤ}
    (h : buildList (List.ofFn f) c e = buildList (List.ofFn f') c' e') :
    f = f' ∧ c = c' ∧ e = e' := by
  have hf := congrArg (fun π : List (List ℤ × ℤ) ↦ π.flatMap fun β => β.1 ++ [β.2]) h
  simp only [buildList_flat] at hf
  obtain ⟨hb, hce⟩ := List.append_inj hf (by simp)
  obtain ⟨hc, he⟩ := List.append_inj' hce rfl
  exact ⟨List.ofFn_injective hb, hc, by simpa using he⟩

/-- The case `c ∉ {4, 5}`: the event `𝒳_{c,o,r}(s)` is parametrised by the words
`b ∈ rawWords (r - 1) (s + o - c)` and the blocks `(c', e)`, through the raw word
`b (c) c' (e)`. -/
private lemma hasSum_of_notMem {s : ℕ} {c o : ℤ} {r : ℕ} (ho : 0 < o) (hoc : o ≤ c)
    (hr : 1 ≤ r) (hc : c ∉ ({4, 5} : Set ℤ)) :
    HasSum (fun π : trRawThreeWitness s c o r ↦ trListWeight π.1)
      (varpi c * rawMass (r - 1) (s + o - c)) := by
  let f : rawWords (r - 1) (s + o - c) × ClosingBlock → List (List ℤ × ℤ) :=
    fun x ↦ buildList (List.ofFn x.1.1) (c :: x.2.1.1) x.2.1.2
  have hf : Function.Injective f := by
    rintro ⟨⟨b, hb⟩, ⟨⟨c₁, e₁⟩, he₁⟩⟩ ⟨⟨b', hb'⟩, ⟨⟨c₁', e₁'⟩, he₁'⟩⟩ h
    obtain ⟨rfl, hc₁, rfl⟩ := ofFn_eq_of_buildList_eq h
    obtain rfl := (List.cons_injective hc₁ : c₁ = c₁')
    rfl
  have hw : ∀ x, trListWeight (f x) = (∏ i, varpi (x.1.1 i)) * varpi c * chBlockWeight x.2.1 := by
    intro x
    simp only [f, buildList_weight, chBlockWeight_cons, varpiIn_of_notMem hc,
      prod_map_varpi_ofFn]
    ring
  refine hasSum_of_parametrisation f hf ?_ (g := fun x ↦
    (∏ i, varpi (x.1.1 i)) * varpi c * chBlockWeight x.2.1) ?_ ?_
  · intro π hπ
    obtain ⟨b, d, e, t, hlen, h2, hs, hdt, hd, he, rfl⟩ := exists_buildList ho hπ
    obtain ⟨d', rfl⟩ : ∃ d', d = c :: d' := by
      rcases d with _ | ⟨x, d'⟩
      · simp only [List.nil_append, List.cons.injEq] at hdt
        exact absurd (hdt.1 ▸ he) hc
      · simp only [List.cons_append, List.cons.injEq] at hdt
        exact ⟨d', by rw [hdt.1]⟩
    obtain ⟨b', rfl⟩ := exists_rawWords hlen h2 hs
    exact ⟨(b', ⟨(d', e), he⟩), rfl⟩
  · intro x
    rw [← hw, indicator_trListWeight_eq]
    intro hne
    obtain ⟨⟨b, hb⟩, ⟨⟨d, e⟩, he⟩⟩ := x
    have hbs : (List.ofFn b).sum = s + o - c := by
      rw [List.sum_ofFn]
      exact (mem_rawWords.mp hb).2
    have hdt : (c :: d) ++ [e] = c :: (d ++ [e]) := List.cons_append ..
    have hmem := buildList_mem hbs ho hoc hdt he hne
    rwa [List.length_ofFn, Nat.sub_add_cancel hr] at hmem
  · rw [rawMass]
    exact hasSum_finset_mul_chBlockWeight (rawWords (r - 1) (s + o - c))
      (fun b ↦ ∏ i, varpi (b i)) (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ varpi_nonneg _)
      (varpi_nonneg c)

/-- The case `c ∈ {4, 5}`: the event `𝒳_{c,o,r}(s)` is parametrised by the words
`b ∈ rawWords (r - 1) (s + o - c)`, through the raw word `b (c)`. -/
private lemma hasSum_of_mem {s : ℕ} {c o : ℤ} {r : ℕ} (ho : 0 < o) (hoc : o ≤ c)
    (hr : 1 ≤ r) (hc : c ∈ ({4, 5} : Set ℤ)) :
    HasSum (fun π : trRawThreeWitness s c o r ↦ trListWeight π.1)
      (varpi c * rawMass (r - 1) (s + o - c)) := by
  let f : rawWords (r - 1) (s + o - c) → List (List ℤ × ℤ) :=
    fun b ↦ buildList (List.ofFn b.1) [] c
  have hf : Function.Injective f := by
    rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
    obtain ⟨rfl, -, -⟩ := ofFn_eq_of_buildList_eq h
    rfl
  have hw : ∀ b, trListWeight (f b) = (∏ i, varpi (b.1 i)) * varpi c := by
    intro b
    simp only [f, buildList_weight, chBlockWeight_nil, prod_map_varpi_ofFn]
  refine hasSum_of_parametrisation f hf ?_ (g := fun b ↦ (∏ i, varpi (b.1 i)) * varpi c) ?_ ?_
  · intro π hπ
    obtain ⟨b, d, e, t, hlen, h2, hs, hdt, hd, he, rfl⟩ := exists_buildList ho hπ
    obtain ⟨rfl, rfl⟩ : d = [] ∧ e = c := by
      rcases d with _ | ⟨x, d'⟩
      · simp only [List.nil_append, List.cons.injEq] at hdt
        exact ⟨rfl, hdt.1⟩
      · simp only [List.cons_append, List.cons.injEq] at hdt
        exact absurd (hdt.1 ▸ hc) (hd x (by simp))
    obtain ⟨b', rfl⟩ := exists_rawWords hlen h2 hs
    exact ⟨b', rfl⟩
  · intro b
    rw [← hw, indicator_trListWeight_eq]
    intro hne
    have hbs : (List.ofFn b.1).sum = s + o - c := by
      rw [List.sum_ofFn]
      exact (mem_rawWords.mp b.2).2
    have hdt : ([] : List ℤ) ++ [c] = c :: [] := rfl
    have hmem := buildList_mem hbs ho hoc hdt hc hne
    rwa [List.length_ofFn, Nat.sub_add_cancel hr] at hmem
  · convert hasSum_fintype (fun b : rawWords (r - 1) (s + o - c) ↦ (∏ i, varpi (b.1 i)) * varpi c)
      using 1
    rw [Finset.sum_coe_sort (rawWords (r - 1) (s + o - c)) (fun b ↦ (∏ i, varpi (b i)) * varpi c),
      ← Finset.sum_mul, ← rawMass, mul_comm]

/-! ### The mass of the first raw crossing events -/

/-- **Mass of the first raw crossing events.** For every `s ∈ ℕ` and all integers `c, o, r` with
`1 ≤ o ≤ c` and `r ≥ 1`, the series `∑_{π ∈ 𝒳_{c,o,r}(s)} bw^⊗(π)` converges to
`ϖ(c) 𝖱(r - 1, s + o - c)`. -/
@[collatz_pos_dens "lem_tr_passage_raw3"]
theorem hasSum_trListWeight_trRawThreeWitness (s : ℕ) {c o : ℤ} {r : ℕ} (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) :
    HasSum (fun π : trRawThreeWitness s c o r ↦ trListWeight π.1)
      (varpi c * rawMass (r - 1) (s + o - c)) := by
  by_cases hc : c ∈ ({4, 5} : Set ℤ)
  · exact hasSum_of_mem (by omega) hoc hr hc
  · exact hasSum_of_notMem (by omega) hoc hr hc

/-- **Mass of the first raw crossing events**, as a `tsum`:
`∑_{π ∈ 𝒳_{c,o,r}(s)} bw^⊗(π) = ϖ(c) 𝖱(r - 1, s + o - c)`. -/
theorem tsum_trListWeight_trRawThreeWitness (s : ℕ) {c o : ℤ} {r : ℕ} (ho : 1 ≤ o)
    (hoc : o ≤ c) (hr : 1 ≤ r) :
    ∑' π : trRawThreeWitness s c o r, trListWeight π.1 = varpi c * rawMass (r - 1) (s + o - c) :=
  (hasSum_trListWeight_trRawThreeWitness s ho hoc hr).tsum_eq

end CollatzPosDens
