/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpWord
public import CollatzPosDens.Renewal.RnFpLaw

/-!
# The support of the first-passage law

If the first-passage law `firstPassageLaw s` is nonzero at `(r, ℓ) ∈ ℤ × ℤ`, then `r ≥ 1` and
`ℓ > s`: some first-passage word `h = (h₁, …, h_K)` with `K ≥ 1` has `h₁ + ⋯ + h_K = (r, ℓ)`, so
`r` is a sum of `K` first coordinates, each at least `1`, and `ℓ`, the sum of the second
coordinates, exceeds `s` by the definition of `IsFirstPassageWord`.

## Main results

* `CollatzPosDens.firstPassageLaw_support_one_le_sum_fst`: the first coordinate of the sum
  of a first-passage word is at least `1`.
* `CollatzPosDens.firstPassageLaw_support_lt_sum_snd`: the second coordinate of the sum of
  a first-passage word for level `s` exceeds `s`.
* `CollatzPosDens.firstPassageLaw_support`: if `firstPassageLaw s (r, ℓ) ≠ 0` then `r ≥ 1`
  and `ℓ > s`.

## Implementation notes

The level `s` is taken in `ℤ` rather than in `ℕ`, as in `firstPassageLaw`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The first coordinate of the sum of a first-passage word is at least `1`. -/
theorem firstPassageLaw_support_one_le_sum_fst {s : ℤ} {h : List (ℤ × ℤ)}
    (hh : IsFirstPassageWord s h) : 1 ≤ h.sum.1 := by
  obtain ⟨hne, hmem, -, -⟩ := hh
  induction h with
  | nil => exact absurd rfl hne
  | cons p t ih =>
    have hp : 1 ≤ p.1 := hmem p (by simp)
    rcases t with _ | ⟨q, t⟩
    · simpa using hp
    · have := ih (by simp) fun r hr => hmem r (List.mem_cons_of_mem _ hr)
      simp only [List.sum_cons, Prod.fst_add] at this ⊢
      omega

/-- The second coordinate of the sum of a first-passage word for level `s` exceeds `s`. -/
theorem firstPassageLaw_support_lt_sum_snd {s : ℤ} {h : List (ℤ × ℤ)}
    (hh : IsFirstPassageWord s h) : s < h.sum.2 := by
  rw [show h.sum.2 = (h.map bkL).sum from bkL_list_sum h]
  exact hh.lt_sum

/-- The support of the first-passage law: if `firstPassageLaw s x ≠ 0`, then `1 ≤ x.1` and
`s < x.2`. -/
@[collatz_pos_dens "lem_rn_fp_support"]
theorem firstPassageLaw_support {s : ℤ} {x : ℤ × ℤ} (hx : firstPassageLaw s x ≠ 0) :
    1 ≤ x.1 ∧ s < x.2 := by
  by_contra hc
  apply hx
  have : IsEmpty {h : List (ℤ × ℤ) // IsFirstPassageWord s h ∧ h.sum = x} :=
    ⟨fun h => hc ⟨h.2.2 ▸ firstPassageLaw_support_one_le_sum_fst h.2.1,
      h.2.2 ▸ firstPassageLaw_support_lt_sum_snd h.2.1⟩⟩
  simp [firstPassageLaw]

end CollatzPosDens
