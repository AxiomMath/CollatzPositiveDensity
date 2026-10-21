/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Seed.S05ConcatWord
public import CollatzPosDens.Recipe.PhConductor

/-!
# The length of a selected concatenated word

For every selected central tuple `τ ∈ 𝔗_{N_*}`, the concatenated word `ŵ(τ)` is short enough
that `|ŵ(τ)| + k_{N_*} ≤ q_*`. Each block `w_j ∈ 𝒞(b_j, K_j)`, `0 ≤ j < N_*`, has length at
most the block length bound `len⁺(b_j)`: below `2^40` because `w_j` is a first-crossing word, so
`|w_j| ≤ h_{b_j}`, and from `2^40` on by the length window `|w_j| ≤ b_j + wd(b_j)` of the
central family. Summing over `0 ≤ j < N_*` and comparing with the conductor gives the bound.

## Main results

* `CollatzPosDens.length_le_lenPlus_of_mem_centralFamily`: `|w| ≤ len⁺(b)` for
  `w ∈ 𝒞(b, K)`.
* `CollatzPosDens.length_concatWord_add_level_lt_conductor`: the strict bound
  `|ŵ(τ)| + k_{N_*} < q_*`.
* `CollatzPosDens.length_concatWord_add_level_le_conductor`: `|ŵ(τ)| + k_{N_*} ≤ q_*`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- A word of the central family `𝒞(b, K)` has length at most `len⁺(b)`. -/
theorem length_le_lenPlus_of_mem_centralFamily {b K : ℕ} {w : Word}
    (hw : w ∈ centralFamily b K) : w.length ≤ lenPlus b := by
  rcases lt_or_ge b (2 ^ 40) with h | h
  · rw [lenPlus_of_lt h]
    exact length_le_hb_of_mem_firstCrossing (centralFamily_subset_firstCrossing b K hw)
  · rw [lenPlus_of_le h]
    exact length_le_add_wd_of_mem_centralFamily hw

/-- For every `τ ∈ 𝔗_{N_*}`, `|ŵ(τ)| + k_{N_*} < q_*`. -/
theorem length_concatWord_add_level_lt_conductor
    {τ : Fin generationThreshold → Word}
    (hτ : τ ∈ selectedTuples generationThreshold) :
    (concatWord τ).length + level generationThreshold < conductor := by
  have hsum : (concatWord τ).length ≤ ∑ j ∈ range generationThreshold, lenPlus (scale j) := by
    rw [length_concatWord]
    calc ∑ k, (τ k).length
        ≤ ∑ k : Fin generationThreshold, lenPlus (scale k) :=
          sum_le_sum fun k _ =>
            length_le_lenPlus_of_mem_centralFamily (selectedTuples_mem_centralFamily hτ k)
      _ = ∑ j ∈ range generationThreshold, lenPlus (scale j) :=
          Fin.sum_univ_eq_sum_range (fun k => lenPlus (scale k)) _
  have := logb_conductor_add_one_lt
  omega

/-- For every `τ ∈ 𝔗_{N_*}`, `|ŵ(τ)| + k_{N_*} ≤ q_*`. -/
@[collatz_pos_dens "lem_s05_tuple_length"]
theorem length_concatWord_add_level_le_conductor
    {τ : Fin generationThreshold → Word}
    (hτ : τ ∈ selectedTuples generationThreshold) :
    (concatWord τ).length + level generationThreshold ≤ conductor :=
  (length_concatWord_add_level_lt_conductor hτ).le

end CollatzPosDens
