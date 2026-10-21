/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkWhite

/-!
# Admissible packets

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For an integer `c` and a point
`p ∈ 𝒫`, the set `Adm_c(p)` of *admissible packets* consists of the pairs `(k, t)` with
`k ∈ ℕ`, `t ∈ {3, 4}` and `k + t ≤ c - 1` such that the point `p - (0, k)` is white for
`n, ξ, ε`. Since `t ≥ 3`, every admissible pair has `k ≤ c - 4`, so `Adm_c(p)` is finite.

## Main definitions

* `CollatzPosDens.chPackets n ξ ε c p`: the finite set `Adm_c(p)`.

## Main results

* `CollatzPosDens.mem_chPackets`: `(k, t) ∈ Adm_c(p)` iff `t ∈ {3, 4}`, `k + t ≤ c - 1` and
  `p - (0, k)` is white.
* `CollatzPosDens.chPackets_eq_empty_of_lt_bkJ`: `Adm_c(p) = ∅` when `j(p) > ⌊n/2⌋`.
* `CollatzPosDens.chPackets_eq_empty_of_le`: `Adm_c(p) = ∅` when `c ≤ 3`.

## Implementation notes

`Adm_c(p)` is a `Finset (ℕ × ℕ)`, obtained by filtering `{0, …, c - 1} × {3, 4}`, so that it can
index finite sums. It is defined for every `p : ℤ × ℤ`, as whiteness is; on `𝒫` it agrees with
the source.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- The set `Adm_c(p)` of admissible packets: the pairs `(k, t) ∈ ℕ × {3, 4}` with
`k + t ≤ c - 1` such that `p - (0, k)` is white for `n, ξ, ε`. -/
@[collatz_pos_dens "def_ch_packets"]
noncomputable def chPackets (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ) (p : ℤ × ℤ) :
    Finset (ℕ × ℕ) :=
  (Finset.range c.toNat ×ˢ {3, 4}).filter fun kt =>
    (kt.1 : ℤ) + kt.2 ≤ c - 1 ∧ IsBkWhite n ξ ε (p - (0, (kt.1 : ℤ)))

/-- `(k, t) ∈ Adm_c(p)` iff `t ∈ {3, 4}`, `k + t ≤ c - 1` and `p - (0, k)` is white. -/
@[simp]
theorem mem_chPackets {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ} {p : ℤ × ℤ}
    {kt : ℕ × ℕ} :
    kt ∈ chPackets n ξ ε c p ↔
      (kt.2 = 3 ∨ kt.2 = 4) ∧ (kt.1 : ℤ) + kt.2 ≤ c - 1 ∧
        IsBkWhite n ξ ε (p - (0, (kt.1 : ℤ))) := by
  obtain ⟨k, t⟩ := kt
  simp only [chPackets, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨-, ht⟩, h⟩
    exact ⟨ht, h⟩
  · rintro ⟨ht, hc, hw⟩
    exact ⟨⟨by omega, ht⟩, hc, hw⟩

/-- Every admissible packet has `t ∈ {3, 4}`. -/
theorem snd_eq_three_or_four_of_mem_chPackets {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ}
    {p : ℤ × ℤ} {kt : ℕ × ℕ} (h : kt ∈ chPackets n ξ ε c p) : kt.2 = 3 ∨ kt.2 = 4 :=
  (mem_chPackets.1 h).1

/-- Every admissible packet satisfies `k + t ≤ c - 1`. -/
theorem add_le_of_mem_chPackets {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ}
    {p : ℤ × ℤ} {kt : ℕ × ℕ} (h : kt ∈ chPackets n ξ ε c p) :
    (kt.1 : ℤ) + kt.2 ≤ c - 1 :=
  (mem_chPackets.1 h).2.1

/-- For every admissible packet `(k, t)`, the point `p - (0, k)` is white. -/
theorem isBkWhite_of_mem_chPackets {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ}
    {p : ℤ × ℤ} {kt : ℕ × ℕ} (h : kt ∈ chPackets n ξ ε c p) :
    IsBkWhite n ξ ε (p - (0, (kt.1 : ℤ))) :=
  (mem_chPackets.1 h).2.2

/-- Every admissible packet `(k, t)` has `k ≤ c - 4`. -/
theorem fst_le_of_mem_chPackets {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ}
    {p : ℤ × ℤ} {kt : ℕ × ℕ} (h : kt ∈ chPackets n ξ ε c p) : (kt.1 : ℤ) ≤ c - 4 := by
  obtain ⟨ht, hc, -⟩ := mem_chPackets.1 h
  omega

/-- `Adm_c(p)` is empty when `j(p) > ⌊n/2⌋`, as no point `p - (0, k)` is then white. -/
theorem chPackets_eq_empty_of_lt_bkJ {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ}
    {p : ℤ × ℤ} (hp : ((n / 2 : ℕ) : ℤ) < bkJ p) : chPackets n ξ ε c p = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun kt h => ?_
  have := (isBkWhite_of_mem_chPackets h).bkJ_le
  simp only [bkJ, Prod.fst_sub, sub_zero] at this hp
  omega

/-- `Adm_c(p)` is empty when `c ≤ 3`. -/
theorem chPackets_eq_empty_of_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ}
    {p : ℤ × ℤ} (hc : c ≤ 3) : chPackets n ξ ε c p = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun kt h => ?_
  have := fst_le_of_mem_chPackets h
  omega

end CollatzPosDens
