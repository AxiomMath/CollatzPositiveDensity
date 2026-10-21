/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrRaw3Witness
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# A first raw crossing happens in the last block

Let `s ∈ ℕ`, let `c, o, r` be integers with `c ≥ 2`, `1 ≤ o ≤ c`, `r ≥ 1`, and let
`π = ((c¹, e¹), …, (cᵏ, eᵏ)) ∈ 𝒳_{c,o,r}(s)`. Write `m = |cᵏ|`, `aᵢ = cᵏᵢ` for `1 ≤ i ≤ m` and
`a_{m+1} = eᵏ`. Then the crossing position `r` lies in the last block: there is
`1 ≤ i ≤ m + 1` with `aᵢ = c` and `(r, s + o) = Bp_{k-1}(π) + (i, a₁ + ⋯ + aᵢ)`.

The proof is short. Write the raw word as `z = z' cᵏ eᵏ` with `z'` the concatenation of the
first `k - 1` blocks, of length `L = j(Bp_{k-1}(π))` and letter sum `l(Bp_{k-1}(π)) ≤ s`. Since
`π` is live, all its letters are at least `2`, so the raw partial sums are nondecreasing on
`z'`; as `σ_r(π) = s + o > s`, the position `r` is not inside `z'`. So `r = L + i` with
`1 ≤ i ≤ m + 1`, the `r`-th letter is `aᵢ`, and `σ_r(π) = l(Bp_{k-1}(π)) + a₁ + ⋯ + aᵢ`.

## Main results

* `CollatzPosDens.trRawThreeWitness_lastBlock`: the statement above.

## Implementation notes

Lists of blocks are `List (List ℤ × ℤ)`. The last block `(cᵏ, eᵏ)` is named through
`π.getLast? = some (cᵏ, eᵏ)`, which always holds for a nonempty `π`, and the word `a₁ ⋯ a_{m+1}` is
the Lean list `cᵏ ++ [eᵏ]`. Letters are indexed from `1`, so `aᵢ` is the entry of index `i - 1`.
Points of the block path live in `ℤ × ℤ`, so `r` is cast to `ℤ`. The statement is proved under the
single side condition `0 < o`: the conditions `c ≥ 2`, `o ≤ c` and `r ≥ 1` are not used (`r ≥ 1`
follows from `σ_r(π) = s + o > 0`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The raw word of a list of blocks of nonzero weight has nonnegative tail sums. -/
theorem sum_drop_flatMap_nonneg {π : List (List ℤ × ℤ)} (h : ∀ b ∈ π, chBlockWeight b ≠ 0)
    (n : ℕ) : 0 ≤ ((π.flatMap fun b => b.1 ++ [b.2]).drop n).sum :=
  List.sum_nonneg fun x hx ↦ by
    obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp (List.mem_of_mem_drop hx)
    have := two_le_of_mem_append_of_chBlockWeight_ne_zero (h b hb) hxb
    omega

/-- A first raw crossing event `π = ((c¹, e¹), …, (cᵏ, eᵏ)) ∈ 𝒳_{c,o,r}(s)` with `0 < o`
crosses in its last block: writing `a = cᵏ eᵏ = (a₁, …, a_{m+1})`, there is `1 ≤ i ≤ m + 1`
with `aᵢ = c` and `(r, s + o) = Bp_{k-1}(π) + (i, a₁ + ⋯ + aᵢ)`. -/
@[collatz_pos_dens "lem_tr_raw3_last_block"]
theorem trRawThreeWitness_lastBlock {s : ℕ} {c o : ℤ} {r : ℕ} (ho : 0 < o)
    {π : List (List ℤ × ℤ)} (hπ : π ∈ trRawThreeWitness s c o r) {d : List ℤ} {e : ℤ}
    (hlast : π.getLast? = some (d, e)) :
    ∃ i, 1 ≤ i ∧ i ≤ d.length + 1 ∧ (d ++ [e])[i - 1]? = some c ∧
      ((r : ℤ), (s : ℤ) + o) =
        chBlockPath π (π.length - 1) + ((i : ℤ), ((d ++ [e]).take i).sum) := by
  obtain ⟨hlt, hc⟩ := trRawThreeWitness_getElem_flatMap hπ
  have h3 : (π.flatMap fun b => b.1 ++ [b.2])[r - 1]? = some c :=
    List.getElem?_eq_some_iff.mpr ⟨hlt, hc⟩
  have hs := trRawThreeWitness_lt_trRawSum hπ ho
  have hσ := trRawThreeWitness_trRawSum hπ
  have hP := trRawThreeWitness_mem_trPassage hπ
  have hlive := trLive_of_mem_trPassage hP
  obtain ⟨π₀, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (π₀ ++ [(d, e)]).length - 1 = π₀.length := by simp
  have hBp : chBlockPath (π₀ ++ [(d, e)]) π₀.length = chBlockPath π₀ π₀.length :=
    chBlockPath_append_of_le _ _ le_rfl
  have hle : (chBlockPath (π₀ ++ [(d, e)]) π₀.length).2 ≤ s :=
    chBlockPath_snd_le_of_mem_trPassage hP (by simp)
  rw [hBp, ← sum_flatMap_eq_chBlockPath_snd] at hle
  have hz : ((π₀ ++ [(d, e)]).flatMap fun b => b.1 ++ [b.2]) =
      (π₀.flatMap fun b => b.1 ++ [b.2]) ++ (d ++ [e]) := by simp
  set z₀ := π₀.flatMap fun b => b.1 ++ [b.2] with hz₀
  have hfst : (chBlockPath π₀ π₀.length).1 = (z₀.length : ℤ) := by
    rw [← toNat_chBlockPath_fst, Int.toNat_of_nonneg (chBlockPath_fst_nonneg _ _)]
  rw [trRawSum_eq_sum_take, hz] at hs hσ
  rw [hz] at h3 hlt
  simp only [List.length_append, List.length_singleton] at hlt
  rw [hlen, hBp, ← hσ]
  by_cases hIL : r ≤ z₀.length
  · exfalso
    rw [List.take_append_of_le_length hIL] at hs
    have hnn : 0 ≤ (z₀.drop r).sum :=
      sum_drop_flatMap_nonneg (fun b hb ↦ hlive b (by simp [hb])) r
    have hsplit := congrArg List.sum (List.take_append_drop r z₀)
    rw [List.sum_append] at hsplit
    omega
  · push Not at hIL
    rw [List.getElem?_append_right (by omega)] at h3
    refine ⟨r - z₀.length, by omega, by omega, ?_, ?_⟩
    · rwa [show r - z₀.length - 1 = r - 1 - z₀.length by omega]
    · rw [List.take_append, List.take_of_length_le (by omega), List.sum_append]
      ext
      · simp only [Prod.fst_add, hfst]
        omega
      · simp only [Prod.snd_add, hz₀, sum_flatMap_eq_chBlockPath_snd]

end CollatzPosDens
