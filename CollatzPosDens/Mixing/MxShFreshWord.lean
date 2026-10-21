/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShFresh

/-!
# The fresh word is a word

Let `N ∈ ℕ` and `w = (a₁, …, a_n)` a word with `d = |Ex_N(w)| < n`. The partial sums
`S_i = A(w_{≤ i})` are strictly increasing, so `S_i ≤ N` exactly for `i ≤ d`; in particular
`S_{d+1} > N`. Hence the first entry `S_{d+1} - N` of the fresh word `Fr_N(w)` is a positive
integer, and its other entries are letters of `w`: `Fr_N(w) ∈ ℤ_{≥1}^{n-d}`.

## Main results

* `CollatzPosDens.Word.freshSeq_mem_words`: `Fr_N(w)` has length `n - d` and positive entries.
* `CollatzPosDens.Word.map_fresh`: the word `fresh N w` has `Fr_N(w)` as its integer sequence.
* `CollatzPosDens.Word.length_fresh`: `|fresh N w| = n - d`.
* `CollatzPosDens.Word.valSum_fresh`: `A(fresh N w) + N = A(w)`.

## Implementation notes

All results are read off from the decomposition `w = u a r` with `A(u) ≤ N < A(u) + a`
(`CollatzPosDens.Word.exists_eq_append_cons_of_card_exposedPattern_lt`), for which
`Ex_N(w) = Pt(u)` and `Fr_N(w) = (A(u) + a - N, r)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

open Finset

/-- **The fresh word is a word.** If `|Ex_N(w)| < |w|`, then `Fr_N(w) ∈ ℤ_{≥1}^{n-d}` with
`n = |w|` and `d = |Ex_N(w)|`: it has `n - d` entries, all at least `1`. -/
@[collatz_pos_dens "lem_mx_sh_fresh_word"]
theorem freshSeq_mem_words {N : ℕ} {w : Word} (h : #(exposedPattern N w) < w.length) :
    (freshSeq N w).length = w.length - #(exposedPattern N w) ∧ ∀ x ∈ freshSeq N w, 1 ≤ x := by
  obtain ⟨u, a, r, rfl, hu, ha⟩ := exists_eq_append_cons_of_card_exposedPattern_lt h
  rw [freshSeq_append_cons r hu ha, card_exposedPattern_append_cons r hu ha]
  refine ⟨by simp, ?_⟩
  simp only [List.mem_cons, List.mem_map]
  rintro x (rfl | ⟨b, -, rfl⟩)
  · omega
  · exact_mod_cast b.pos

/-- If `|Ex_N(w)| < |w|`, the word `fresh N w` has the integer sequence `Fr_N(w)`. -/
theorem map_fresh {N : ℕ} {w : Word} (h : #(exposedPattern N w) < w.length) :
    (fresh N w).map (fun a : ℕ+ => ((a : ℕ) : ℤ)) = freshSeq N w := by
  obtain ⟨u, a, r, rfl, hu, ha⟩ := exists_eq_append_cons_of_card_exposedPattern_lt h
  rw [freshSeq_append_cons r hu ha, fresh_append_cons r hu ha, List.map_cons,
    coe_toPNat'_valSum_add_sub ha]
  congr 1
  omega

/-- If `|Ex_N(w)| < |w|`, then `|fresh N w| = |w| - |Ex_N(w)|`. -/
theorem length_fresh {N : ℕ} {w : Word} (h : #(exposedPattern N w) < w.length) :
    (fresh N w).length = w.length - #(exposedPattern N w) := by
  rw [← (freshSeq_mem_words h).1, ← map_fresh h, List.length_map]

/-- If `|Ex_N(w)| < |w|`, then `A(fresh N w) + N = A(w)`. -/
theorem valSum_fresh {N : ℕ} {w : Word} (h : #(exposedPattern N w) < w.length) :
    valSum (fresh N w) + N = valSum w := by
  obtain ⟨u, a, r, rfl, hu, ha⟩ := exists_eq_append_cons_of_card_exposedPattern_lt h
  exact valSum_fresh_append_cons r hu ha

end Word

end CollatzPosDens
