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
public import CollatzPosDens.StoppingTrace.TrFirstRaw
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrRaw3Witness
public import CollatzPosDens.StoppingTrace.TrRawSum

/-!
# A raw-three witness crosses in its last block

Let `s ∈ ℕ` and let `π = ((c¹, e¹), …, (cᵏ, eᵏ)) ∈ 𝒜₃(s)` be a raw-three witness. The letter
`3` read at the first raw crossing `i_s(π)` of the raw word `z = c¹ e¹ ⋯ cᵏ eᵏ` is a nonclosing
letter of the last block: there is `1 ≤ i ≤ |cᵏ|` with `cᵏᵢ = 3` and
`(i_s(π), σ_{i_s(π)}(π)) = Bp_{k-1}(π) + (i, cᵏ₁ + ⋯ + cᵏᵢ)`.

Write `z = z' cᵏ eᵏ` with `z'` the concatenation of the first `k - 1` blocks, of length
`L = j(Bp_{k-1}(π))` and letter sum `l(Bp_{k-1}(π)) ≤ s`. Since `π` is live, all its letters are
at least `2`, so the raw partial sums are nondecreasing on `z'`; as `σ_{i_s(π)}(π) > s`, the
crossing cannot happen inside `z'`. It cannot happen at the closing letter `eᵏ ≠ 3` either, so it
happens at a position `L + i` with `1 ≤ i ≤ |cᵏ|`.

## Main results

* `CollatzPosDens.trRawThreeWitness_lastBlock`: a raw-three witness crosses level `s` at a
  nonclosing letter `3` of its last block.

## Implementation notes

Lists of blocks are `List (List ℤ × ℤ)`; the condition `eᵏ ∈ {4, 5}` coming from `π ∈ 𝔅ᵏ` is
part of membership in `Π_s` (`trRawThreeWitness_closing_mem`), and only its consequence `eᵏ ≠ 3`
is used. The last block `(cᵏ, eᵏ)` is named through `π.getLast? = some (cᵏ, eᵏ)`, which always
holds for a nonempty `π`. Letters are indexed from `1`, so `cᵏᵢ` is the entry `cᵏ[i - 1]` of the
Lean list. Points of the block path live in `ℤ × ℤ`, so `i_s(π)` is cast to `ℤ`.

## References

* [Mazur, *Collatz positive density*], §9.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- A raw-three witness `π = ((c¹, e¹), …, (cᵏ, eᵏ)) ∈ 𝒜₃(s)` crosses level `s` at a
nonclosing letter `3` of its last block: there is `1 ≤ i ≤ |cᵏ|` with `cᵏᵢ = 3` and
`(i_s(π), σ_{i_s(π)}(π)) = Bp_{k-1}(π) + (i, cᵏ₁ + ⋯ + cᵏᵢ)`. -/
@[collatz_pos_dens "lem_tr_raw3_last_block"]
theorem trRawThreeWitness_lastBlock {s : ℕ} {π : List (List ℤ × ℤ)}
    (hπ : π ∈ trRawThreeWitness s) {c : List ℤ} {e : ℤ}
    (hlast : π.getLast? = some (c, e)) :
    ∃ i, 1 ≤ i ∧ i ≤ c.length ∧ c[i - 1]? = some 3 ∧
      (((trFirstRaw s π : ℕ) : ℤ), trRawSum π (trFirstRaw s π)) =
        chBlockPath π (π.length - 1) + ((i : ℤ), (c.take i).sum) := by
  have h3 : (π.flatMap fun b => b.1 ++ [b.2])[trFirstRaw s π - 1]? = some 3 := by
    obtain ⟨hlt, h3⟩ := trRawThreeWitness_getElem_flatMap hπ
    exact List.getElem?_eq_some_iff.mpr ⟨hlt, h3⟩
  have hone := trRawThreeWitness_one_le_trFirstRaw hπ
  have hs := trRawThreeWitness_lt_trRawSum hπ
  have hP := trRawThreeWitness_mem_trPassage hπ
  have hlive := trLive_of_mem_trPassage hP
  set I := trFirstRaw s π with hI
  clear_value I
  obtain ⟨π₀, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hlen : (π₀ ++ [(c, e)]).length - 1 = π₀.length := by simp
  have hBp : chBlockPath (π₀ ++ [(c, e)]) π₀.length = chBlockPath π₀ π₀.length :=
    chBlockPath_append_of_le _ _ le_rfl
  have hle : (chBlockPath (π₀ ++ [(c, e)]) π₀.length).2 ≤ s :=
    chBlockPath_snd_le_of_mem_trPassage hP (by simp)
  rw [hBp, ← sum_flatMap_eq_chBlockPath_snd] at hle
  have hz : ((π₀ ++ [(c, e)]).flatMap fun b => b.1 ++ [b.2]) =
      (π₀.flatMap fun b => b.1 ++ [b.2]) ++ (c ++ [e]) := by simp
  set z₀ := π₀.flatMap fun b => b.1 ++ [b.2] with hz₀
  have hfst : (chBlockPath π₀ π₀.length).1 = (z₀.length : ℤ) := by
    rw [← toNat_chBlockPath_fst, Int.toNat_of_nonneg (chBlockPath_fst_nonneg _ _)]
  rw [trRawSum_eq_sum_take, hz] at hs ⊢
  rw [hz] at h3
  rw [hlen, hBp]
  by_cases hIL : I ≤ z₀.length
  · exfalso
    rw [List.take_append_of_le_length hIL] at hs
    have hnn : 0 ≤ (z₀.drop I).sum := by
      refine List.sum_nonneg fun x hx ↦ ?_
      obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp (List.mem_of_mem_drop hx)
      have := two_le_of_mem_append_of_chBlockWeight_ne_zero (hlive b (by simp [hb])) hxb
      omega
    have hsplit := congrArg List.sum (List.take_append_drop I z₀)
    rw [List.sum_append] at hsplit
    omega
  · push Not at hIL
    have hpos : z₀.length ≤ I - 1 := by omega
    rw [List.getElem?_append_right hpos] at h3
    by_cases hc : I - 1 - z₀.length < c.length
    · rw [List.getElem?_append_left hc] at h3
      refine ⟨I - z₀.length, by omega, by omega, ?_, ?_⟩
      · rwa [show I - z₀.length - 1 = I - 1 - z₀.length by omega]
      · have hI' : I = z₀.length + (I - z₀.length) := by omega
        rw [hI', List.take_append, List.take_of_length_le (by omega), List.sum_append,
          Nat.add_sub_cancel_left, List.take_append_of_le_length (by omega)]
        ext
        · simp only [Prod.fst_add, hfst]; push_cast; omega
        · simp only [Prod.snd_add, hz₀, sum_flatMap_eq_chBlockPath_snd]
    · exfalso
      push Not at hc
      rw [List.getElem?_append_right hc] at h3
      simp only [List.getElem?_singleton] at h3
      split_ifs at h3
      have he := trRawThreeWitness_closing_mem hπ (b := (c, e)) (by simp)
      rw [Option.some_injective _ h3] at he
      norm_num at he

end CollatzPosDens
