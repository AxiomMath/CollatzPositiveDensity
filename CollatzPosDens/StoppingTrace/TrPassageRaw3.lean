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
public import CollatzPosDens.Renewal.RnP3
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.StoppingTrace.TrFirstRaw
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrRaw3LastBlock
public import CollatzPosDens.StoppingTrace.TrRaw3Witness
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# Mass of the raw-three witnesses

For `s ∈ ℕ`, the raw-three witnesses `𝒜₃(s)` carry total weight `p₃(s)`:
`∑_{π ∈ 𝒜₃(s)} bw^⊗(π) = p₃(s)`.

Write `f = ⌊(5s + 16)/16⌋`. A raw-three witness `π` is described by a tuple `(r, O, b, c, e)`
with `1 ≤ r ≤ f`, `O ∈ {1, 2, 3}`, a word `b ∈ ℤ^{r-1}` with letters `≥ 2` and sum `s + O - 3`,
a block `(c, e)` with `e ∈ {4, 5}`: its raw word is `b (3) c (e)`, cut after each letter in
`{4, 5}`. Indeed, by `trRawThreeWitness_lastBlock` the letter `3` read at the first raw
crossing `r = i_s(π)` is a nonclosing letter of the last block, so `b` is the raw word before
it and `(c, e)` the rest of the last block. Conversely, cutting `b (3) c (e)` after its letters
in `{4, 5}` gives a passage list as soon as its weight is nonzero: the block endpoints before
the last lie inside `b`, at height at most `s + O - 3 ≤ s`, and the first raw crossing is at
position `r`, where the partial sum is `s + O`. The weight of the list is
`∏ ϖ(bᵢ) · ϖ(3) · bw(c, e)`, so summing over the tuples gives
`ϖ(3) ∑_{O=1}^{3} ∑_{r=1}^{f} 𝖱(r - 1, s + O - 3) · ∑_{(c, e) ∈ 𝔅} bw(c, e) = p₃(s)`,
since the block weights have total mass `1`.

## Main results

* `CollatzPosDens.hasSum_trListWeight_trRawThreeWitness`: the series
  `∑_{π ∈ 𝒜₃(s)} bw^⊗(π)` converges (unconditionally) to `p₃(s)`.
* `CollatzPosDens.tsum_trListWeight_trRawThreeWitness`: the same identity for `tsum`.

## Implementation notes

The sum over `𝒜₃(s)` is stated as a `HasSum` over the subtype `trRawThreeWitness s`; this
records the convergence of the series as well as its value, and since the terms are
nonnegative it is the strongest form of the statement (it implies the identity in `[0, ∞]`).
Rather than summing the factor `(∑_{a ∉ {4, 5}} ϖ(a))^m (ϖ(4) + ϖ(5))` over `m ≥ 0`, the
tuples carry the whole block `(c, e)` and its weight `bw(c, e)`, which already vanishes when a
letter of `c` lies in `{4, 5}`, and the factor is the total block mass
`hasSum_prod_chBlockWeight_single`. The tuples whose block `(c, e)` has weight zero are kept:
their list has weight zero too, so they do not contribute. This makes the tuple-to-list map
injective on all tuples, which is what `Function.Injective.hasSum_iff` needs.

## References

* [Mazur, *Collatz positive density*], §9.3.
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

/-! ### The list attached to a tuple -/

/-- The list of blocks with raw word `b (3) c (e)`, cut after the letters of `b` in `{4, 5}` and
after the final letter `e`. -/
private def build (b c : List ℤ) (e : ℤ) : List (List ℤ × ℤ) :=
  (cutBlocks [] b).1 ++ [((cutBlocks [] b).2 ++ 3 :: c, e)]

private lemma build_flat (b c : List ℤ) (e : ℤ) :
    ((build b c e).flatMap fun b => b.1 ++ [b.2]) = b ++ 3 :: (c ++ [e]) := by
  have h := cutBlocks_flat [] b
  rw [List.nil_append] at h
  conv_rhs => rw [← h]
  simp [build]

private lemma build_length (b c : List ℤ) (e : ℤ) :
    (build b c e).length = (cutBlocks [] b).1.length + 1 := by
  simp [build]

private lemma build_weight (b c : List ℤ) (e : ℤ) :
    trListWeight (build b c e) = (b.map varpi).prod * varpi 3 * chBlockWeight (c, e) := by
  have h := cutBlocks_weight [] b
  simp only [List.map_nil, List.prod_nil, one_mul] at h
  have h3 : varpiIn 3 = varpi 3 := varpiIn_of_notMem (by norm_num)
  rw [build, trListWeight_concat, chBlockWeight_append, chBlockWeight_cons]
  change _ * (_ * (varpiIn 3 * _)) = _
  rw [h3]
  linear_combination (varpi 3 * chBlockWeight (c, e)) * h

private lemma build_closing {b c : List ℤ} {e : ℤ} (he : e ∈ ({4, 5} : Set ℤ)) :
    ∀ x ∈ build b c e, x.2 ∈ ({4, 5} : Set ℤ) := by
  intro x hx
  simp only [build, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact cutBlocks_closing [] b x hx
  · exact he

private lemma sum_map_eq_sum_flat (β : List (List ℤ × ℤ)) :
    (β.map fun b => b.1.sum + b.2).sum = (β.flatMap fun b => b.1 ++ [b.2]).sum := by
  induction β with
  | nil => simp
  | cons b β ih => simp [ih, add_assoc]

/-- The first raw crossing of the list attached to `(b, c, e)` is at the letter `3`. -/
private lemma build_trFirstRaw {s : ℕ} {b c : List ℤ} {e : ℤ} (hb : ∀ x ∈ b, 0 ≤ x)
    (hbs : b.sum ≤ s) (hbs' : (s : ℤ) < b.sum + 3) :
    trFirstRaw s (build b c e) = b.length + 1 ∧
      trRawSum (build b c e) (b.length + 1) = b.sum + 3 := by
  have hσ : ∀ i, trRawSum (build b c e) i = ((b ++ 3 :: (c ++ [e])).take i).sum := by
    intro i; rw [trRawSum_eq_sum_take, build_flat]
  have hr : trRawSum (build b c e) (b.length + 1) = b.sum + 3 := by
    rw [hσ, List.take_append, List.take_of_length_le (by omega)]
    simp
  have hle : ∀ i ≤ b.length, trRawSum (build b c e) i ≤ s := by
    intro i hi
    rw [hσ, List.take_append_of_le_length hi]
    exact ((List.take_prefix i b).sublist.sum_le_sum hb).trans hbs
  have hM : b.length + 1 ≤ (chBlockPath (build b c e) (build b c e).length).1.toNat := by
    rw [toNat_chBlockPath_fst, build_flat]
    simp
  refine ⟨le_antisymm (trFirstRaw_le_of_lt (by omega) hM (by rw [hr]; exact hbs')) ?_, hr⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨hmem, hgt⟩ := trFirstRaw_spec (s := s) (π := build b c e)
    ⟨b.length + 1, mem_Icc.mpr ⟨by omega, hM⟩, by rw [hr]; exact hbs'⟩
  rw [mem_Icc] at hmem
  have := hle (trFirstRaw s (build b c e)) (by omega)
  omega

/-- The list attached to `(b, c, e)` is a raw-three witness as soon as its weight is nonzero. -/
private lemma build_mem {s : ℕ} {b c : List ℤ} {e : ℤ} (hb : ∀ x ∈ b, 0 ≤ x)
    (hc : ∀ x ∈ c, 0 ≤ x) (hbs : b.sum ≤ s) (hbs' : (s : ℤ) < b.sum + 3)
    (he : e ∈ ({4, 5} : Set ℤ)) (hr : b.length + 1 ≤ (5 * s + 16) / 16)
    (hw : trListWeight (build b c e) ≠ 0) : build b c e ∈ trRawThreeWitness s := by
  obtain ⟨hI, hσ⟩ := build_trFirstRaw (c := c) (e := e) hb hbs hbs'
  refine ⟨⟨build_closing he, (trLive_iff_prod_ne_zero _).mpr hw, by simp [build], ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · intro i hi
    rw [build_length] at hi
    rw [chBlockPath_snd, build, List.take_append_of_le_length (by omega), sum_map_eq_sum_flat]
    refine (List.IsPrefix.sublist ?_ |>.sum_le_sum hb).trans hbs
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
  · rw [← sum_flatMap_eq_chBlockPath_snd, build_flat]
    have h0 : 0 ≤ c.sum := List.sum_nonneg hc
    have he4 : 4 ≤ e := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he; omega
    simp only [List.sum_append, List.sum_cons, List.sum_nil]
    omega
  · rw [chRaw_toNat_chBlockPath_fst, build_flat, hI]
    simp
  · rw [hI]; exact hr
  · rw [hI, hσ]; omega

/-! ### The tuples -/

/-- The finite set of the triples `(O, r, b)` with `O ∈ {1, 2, 3}`, `1 ≤ r ≤ ⌊(5s+16)/16⌋` and
`b ∈ ℤ^{r-1}` a word with letters `≥ 2` and sum `s + O - 3`. -/
private def tupleSet (s : ℕ) : Finset (Σ p : ℕ × ℕ, Fin (p.2 - 1) → ℤ) :=
  (Icc 1 3 ×ˢ Icc 1 ((5 * s + 16) / 16)).sigma fun p ↦ rawWords (p.2 - 1) ((s : ℤ) + p.1 - 3)

private lemma mem_tupleSet {s : ℕ} {x : Σ p : ℕ × ℕ, Fin (p.2 - 1) → ℤ} :
    x ∈ tupleSet s ↔ (1 ≤ x.1.1 ∧ x.1.1 ≤ 3) ∧ (1 ≤ x.1.2 ∧ x.1.2 ≤ (5 * s + 16) / 16) ∧
      (∀ i, 2 ≤ x.2 i) ∧ ∑ i, x.2 i = (s : ℤ) + x.1.1 - 3 := by
  simp [tupleSet, mem_sigma, mem_product, mem_rawWords, and_assoc]

private lemma tupleSet_facts {s : ℕ} {x : Σ p : ℕ × ℕ, Fin (p.2 - 1) → ℤ}
    (hx : x ∈ tupleSet s) :
    (∀ y ∈ List.ofFn x.2, 0 ≤ y) ∧ (List.ofFn x.2).sum ≤ s ∧
      (s : ℤ) < (List.ofFn x.2).sum + 3 ∧ (List.ofFn x.2).length + 1 = x.1.2 ∧
      (List.ofFn x.2).sum + 3 = s + x.1.1 ∧ x.1.2 ≤ (5 * s + 16) / 16 := by
  obtain ⟨⟨hO1, hO3⟩, ⟨hr1, hrf⟩, h2, hsum⟩ := mem_tupleSet.mp hx
  rw [List.sum_ofFn, hsum, List.length_ofFn]
  refine ⟨fun y hy ↦ ?_, by omega, by omega, by omega, by omega, hrf⟩
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  linarith [h2 i]

private lemma sum_tupleSet (s : ℕ) :
    ∑ x ∈ tupleSet s, (∏ i, varpi (x.2 i)) * varpi 3 = p3 s := by
  rw [tupleSet, sum_sigma, p3, sum_product, mul_sum]
  refine sum_congr rfl fun O _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  rw [← sum_mul, rawMass, mul_comm]

/-! ### The mass of the raw-three witnesses -/

/-- **Mass of the raw-three witnesses.** For every `s ∈ ℕ`, the series
`∑_{π ∈ 𝒜₃(s)} bw^⊗(π)` converges to `p₃(s)`. -/
@[collatz_pos_dens "lem_tr_passage_raw3"]
theorem hasSum_trListWeight_trRawThreeWitness (s : ℕ) :
    HasSum (fun π : trRawThreeWitness s ↦ trListWeight π.1) (p3 s) := by
  let B := {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}
  let Φ : tupleSet s × B → List (List ℤ × ℤ) := fun x ↦
    build (List.ofFn x.1.1.2) x.2.1.1 x.2.1.2
  -- the map from tuples to lists is injective
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨⟨⟨O, r⟩, b⟩, hx⟩, ⟨⟨c, e⟩, he⟩⟩ ⟨⟨⟨⟨O', r'⟩, b'⟩, hx'⟩, ⟨⟨c', e'⟩, he'⟩⟩ h
    simp only [Φ] at h
    obtain ⟨hb0, hbs, hbs', hlen, hsum, -⟩ := tupleSet_facts hx
    obtain ⟨hb0', hbs₁, hbs₁', hlen', hsum', -⟩ := tupleSet_facts hx'
    simp only at hb0 hbs hbs' hlen hsum hb0' hbs₁ hbs₁' hlen' hsum'
    obtain ⟨t1, u1⟩ := build_trFirstRaw (c := c) (e := e) hb0 hbs hbs'
    obtain ⟨t2, u2⟩ := build_trFirstRaw (c := c') (e := e') hb0' hbs₁ hbs₁'
    rw [h, t2] at t1
    rw [h, ← t1, u2] at u1
    have hr : r = r' := by omega
    subst hr
    have hO : O = O' := by omega
    subst hO
    have hf := congrArg (fun π : List (List ℤ × ℤ) ↦ π.flatMap fun b => b.1 ++ [b.2]) h
    simp only [build_flat] at hf
    obtain ⟨hb, hce⟩ := List.append_inj hf (by simp)
    obtain rfl := List.ofFn_injective hb
    obtain ⟨rfl, he⟩ := List.append_inj' (List.cons_injective hce) rfl
    obtain rfl : e = e' := by simpa using he
    rfl
  -- every raw-three witness comes from a tuple
  have hrange : ∀ π ∉ Set.range Φ, (trRawThreeWitness s).indicator trListWeight π = 0 := by
    intro π hπ
    refine Set.indicator_of_notMem (fun hA ↦ hπ ?_) _
    have hP := trRawThreeWitness_mem_trPassage hA
    have hlive := trLive_of_mem_trPassage hP
    have hne := ne_nil_of_mem_trPassage hP
    obtain ⟨π₀, ⟨c, e⟩, rfl⟩ : ∃ π₀ x, π = π₀ ++ [x] :=
      ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
    have hlast : (π₀ ++ [(c, e)]).getLast? = some (c, e) := by simp
    obtain ⟨i, hi1, hic, hci, hpt⟩ := trRawThreeWitness_lastBlock hA hlast
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hci
    obtain ⟨hj, hcj⟩ := List.getElem?_eq_some_iff.mp hci
    set I := trFirstRaw s (π₀ ++ [(c, e)]) with hIdef
    have hlen : (π₀ ++ [(c, e)]).length - 1 = π₀.length := by simp
    rw [hlen, chBlockPath_append_of_le _ _ le_rfl] at hpt
    set z₀ := π₀.flatMap fun b => b.1 ++ [b.2] with hz₀
    have hfst : (chBlockPath π₀ π₀.length).1 = (z₀.length : ℤ) := by
      rw [← toNat_chBlockPath_fst, Int.toNat_of_nonneg (chBlockPath_fst_nonneg _ _)]
    have hsnd : (chBlockPath π₀ π₀.length).2 = z₀.sum := (sum_flatMap_eq_chBlockPath_snd π₀).symm
    have hI : I = z₀.length + (j + 1) := by
      have := congrArg Prod.fst hpt
      simp only [Prod.fst_add, hfst] at this
      omega
    have htake : c.take (j + 1) = c.take j ++ [3] := by
      rw [List.take_add_one, hci]; rfl
    have hσ : trRawSum (π₀ ++ [(c, e)]) I = z₀.sum + (c.take j).sum + 3 := by
      have := congrArg Prod.snd hpt
      simp only [Prod.snd_add, hsnd, htake, List.sum_append, List.sum_cons,
        List.sum_nil] at this
      rw [this]; ring
    have hgt := trRawThreeWitness_lt_trRawSum hA
    have hle3 := trRawThreeWitness_trRawSum_le hA
    have hI1 := trRawThreeWitness_one_le_trFirstRaw hA
    have hIf := trRawThreeWitness_trFirstRaw_le hA
    rw [← hIdef] at hgt hle3 hI1 hIf
    have hlastw : chBlockWeight (c, e) ≠ 0 := hlive _ (by simp)
    have hπ₀ : ∀ b ∈ π₀, (∀ x ∈ b.1, ¬ (x = 4 ∨ x = 5)) ∧ (b.2 = 4 ∨ b.2 = 5) := by
      intro b hb
      refine ⟨fun x hx h ↦
        hlive b (by simp [hb]) (chBlockWeight_eq_zero_of_mem hx (by simpa using h)), ?_⟩
      simpa using trRawThreeWitness_closing_mem hA (b := b) (by simp [hb])
    have hcj' : ∀ x ∈ c.take j, ¬ (x = 4 ∨ x = 5) := fun x hx ↦
      fun h ↦ hlastw (chBlockWeight_eq_zero_of_mem (List.mem_of_mem_take hx) (by simpa using h))
    set bw := z₀ ++ c.take j with hbw
    have hbwlen : bw.length = I - 1 := by
      simp only [hbw, List.length_append, List.length_take]
      omega
    have hbw2 : ∀ x ∈ bw, 2 ≤ x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hx
        exact two_le_of_mem_append_of_chBlockWeight_ne_zero (hlive b (by simp [hb])) hxb
      · exact two_le_of_chBlockWeight_ne_zero hlastw (List.mem_of_mem_take hx)
    have hbwsum : bw.sum + 3 = trRawSum (π₀ ++ [(c, e)]) I := by
      rw [hσ, hbw, List.sum_append]
    set O := (trRawSum (π₀ ++ [(c, e)]) I - s).toNat with hOdef
    have hO : (O : ℤ) = trRawSum (π₀ ++ [(c, e)]) I - s := Int.toNat_of_nonneg (by omega)
    let bf : Fin (I - 1) → ℤ := fun k ↦ bw.getD k 0
    have hofn : List.ofFn bf = bw := by
      refine List.ext_getElem (by simp [hbwlen]) fun n h1 h2 ↦ ?_
      simp [bf, List.getElem?_eq_getElem h2]
    have hmem : (⟨(O, I), bf⟩ : Σ p : ℕ × ℕ, Fin (p.2 - 1) → ℤ) ∈ tupleSet s := by
      rw [mem_tupleSet]
      have hO13 : 1 ≤ O ∧ O ≤ 3 := by omega
      refine ⟨hO13, ⟨hI1, hIf⟩, fun k ↦ hbw2 _ ?_, ?_⟩
      · rw [← hofn]; exact List.mem_ofFn.mpr ⟨k, rfl⟩
      · rw [← List.sum_ofFn, hofn]; simp only; omega
    refine ⟨(⟨⟨(O, I), bf⟩, hmem⟩, ⟨(c.drop (j + 1), e), ?_⟩), ?_⟩
    · exact trRawThreeWitness_closing_mem hA (b := (c, e)) (by simp)
    · change build (List.ofFn bf) (c.drop (j + 1)) e = π₀ ++ [(c, e)]
      rw [hofn, build, hbw, cutBlocks_flat_append π₀ (c.take j) hπ₀ hcj']
      have hd : c.drop j = 3 :: c.drop (j + 1) := by rw [List.drop_eq_getElem_cons hj, hcj]
      simp only
      rw [← hd, List.take_append_drop]
  -- the weight of the list attached to a tuple
  have hcomp : ∀ x : tupleSet s × B, (trRawThreeWitness s).indicator trListWeight (Φ x) =
      (∏ i, varpi (x.1.1.2 i)) * varpi 3 * chBlockWeight x.2.1 := by
    rintro ⟨⟨⟨⟨O, r⟩, b⟩, hx⟩, ⟨⟨c, e⟩, he⟩⟩
    have hw : trListWeight (Φ ⟨⟨⟨(O, r), b⟩, hx⟩, ⟨(c, e), he⟩⟩) =
        (∏ i, varpi (b i)) * varpi 3 * chBlockWeight (c, e) := by
      simp only [Φ, build_weight, List.map_ofFn, List.prod_ofFn, Function.comp_def]
    rw [← hw, Set.indicator_apply_eq_self]
    intro hnot
    by_contra hw0
    obtain ⟨hb0, hbs, hbs', hlen, -, hrf⟩ := tupleSet_facts hx
    simp only at hb0 hbs hbs' hlen hrf
    have hcw : chBlockWeight (c, e) ≠ 0 := by
      intro h0; rw [hw, h0, mul_zero] at hw0; exact hw0 rfl
    refine hnot (build_mem (b := List.ofFn b) (c := c) hb0 (fun x hx ↦ ?_) hbs hbs' he
      (by omega) hw0)
    have := two_le_of_chBlockWeight_ne_zero hcw hx
    omega
  -- the mass of the tuples
  have hsum : HasSum (fun x : tupleSet s × B ↦
      (∏ i, varpi (x.1.1.2 i)) * varpi 3 * chBlockWeight x.2.1) (p3 s) := by
    have h1 : HasSum (fun a : tupleSet s ↦ (∏ i, varpi (a.1.2 i)) * varpi 3)
        (∑ a : tupleSet s, (∏ i, varpi (a.1.2 i)) * varpi 3) := hasSum_fintype _
    have h2 := hasSum_prod_chBlockWeight_single
    have h := h1.mul h2 (Summable.mul_of_nonneg h1.summable h2.summable
      (fun a ↦ mul_nonneg (prod_nonneg fun _ _ ↦ varpi_nonneg _) (varpi_nonneg _))
      (fun β ↦ chBlockWeight_nonneg _))
    rwa [mul_one, sum_coe_sort (tupleSet s) (fun a ↦ (∏ i, varpi (a.2 i)) * varpi 3),
      sum_tupleSet] at h
  rw [show (fun π : trRawThreeWitness s ↦ trListWeight π.1) = trListWeight ∘ Subtype.val
    from rfl, hasSum_subtype_iff_indicator, ← hinj.hasSum_iff hrange]
  convert hsum using 1
  exact funext hcomp

/-- **Mass of the raw-three witnesses**, as a `tsum`: `∑_{π ∈ 𝒜₃(s)} bw^⊗(π) = p₃(s)`. -/
theorem tsum_trListWeight_trRawThreeWitness (s : ℕ) :
    ∑' π : trRawThreeWitness s, trListWeight π.1 = p3 s :=
  (hasSum_trListWeight_trRawThreeWitness s).tsum_eq

end CollatzPosDens
