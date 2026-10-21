/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPackets

/-!
# Packet coverage

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For an integer `c` and a point `p`, the
*packet coverage* `M_c(p)` is the largest total length `∑_{(k,t) ∈ S} t` of a family
`S ⊆ Adm_c(p)` of admissible packets whose index sets `{k, …, k + t - 1}` are pairwise disjoint.
As `Adm_c(p)` is finite and the empty family is admissible, this maximum exists in `ℕ`.

## Main definitions

* `CollatzPosDens.chPacketCoverage n ξ ε c p`: the packet coverage `M_c(p)`.

## Main results

* `CollatzPosDens.sum_le_chPacketCoverage`: every family of admissible packets with pairwise
  disjoint index sets has total length at most `M_c(p)`.
* `CollatzPosDens.exists_sum_eq_chPacketCoverage`: some such family has total length exactly
  `M_c(p)`.
* `CollatzPosDens.isGreatest_chPacketCoverage`: `M_c(p)` is the greatest such total length.
* `CollatzPosDens.chPacketCoverage_eq_zero_of_le`: `M_c(p) = 0` when `c ≤ 3`.

## Implementation notes

The maximum is taken as a `Finset.sup` in `ℕ` over the subfamilies of `Adm_c(p)` with pairwise
disjoint index sets; the empty family contributes `0`, the bottom element, so the supremum is the
maximum of the source.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

open Classical in
/-- The packet coverage `M_c(p)`: the largest value of `∑_{(k,t) ∈ S} t` over the families
`S ⊆ Adm_c(p)` whose index sets `{k, …, k + t - 1}` are pairwise disjoint. -/
@[collatz_pos_dens "def_ch_packet_coverage"]
noncomputable def chPacketCoverage (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ) (p : ℤ × ℤ) :
    ℕ :=
  ((chPackets n ξ ε c p).powerset.filter fun S : Finset (ℕ × ℕ) =>
      (S : Set (ℕ × ℕ)).PairwiseDisjoint fun kt => Finset.Ico kt.1 (kt.1 + kt.2)).sup
    fun S => ∑ kt ∈ S, kt.2

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ} {p : ℤ × ℤ}

/-- Every family of admissible packets with pairwise disjoint index sets has total length at
most `M_c(p)`. -/
theorem sum_le_chPacketCoverage {S : Finset (ℕ × ℕ)} (hS : S ⊆ chPackets n ξ ε c p)
    (hd : (S : Set (ℕ × ℕ)).PairwiseDisjoint fun kt => Finset.Ico kt.1 (kt.1 + kt.2)) :
    ∑ kt ∈ S, kt.2 ≤ chPacketCoverage n ξ ε c p := by
  classical
  unfold chPacketCoverage
  exact Finset.le_sup (f := fun S : Finset (ℕ × ℕ) => ∑ kt ∈ S, kt.2)
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hS, hd⟩)

/-- Some family of admissible packets with pairwise disjoint index sets has total length exactly
`M_c(p)`. -/
theorem exists_sum_eq_chPacketCoverage :
    ∃ S ⊆ chPackets n ξ ε c p,
      (S : Set (ℕ × ℕ)).PairwiseDisjoint (fun kt => Finset.Ico kt.1 (kt.1 + kt.2)) ∧
        ∑ kt ∈ S, kt.2 = chPacketCoverage n ξ ε c p := by
  classical
  unfold chPacketCoverage
  obtain ⟨S, hS, h⟩ := Finset.exists_mem_eq_sup
    ((chPackets n ξ ε c p).powerset.filter fun S : Finset (ℕ × ℕ) =>
      (S : Set (ℕ × ℕ)).PairwiseDisjoint fun kt => Finset.Ico kt.1 (kt.1 + kt.2))
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp⟩⟩
    fun S => ∑ kt ∈ S, kt.2
  obtain ⟨hS, hd⟩ := Finset.mem_filter.1 hS
  exact ⟨S, Finset.mem_powerset.1 hS, hd, by convert h.symm⟩

/-- `M_c(p)` is the greatest total length of a family of admissible packets with pairwise
disjoint index sets. -/
theorem isGreatest_chPacketCoverage :
    IsGreatest {m | ∃ S ⊆ chPackets n ξ ε c p,
      (S : Set (ℕ × ℕ)).PairwiseDisjoint (fun kt => Finset.Ico kt.1 (kt.1 + kt.2)) ∧
        ∑ kt ∈ S, kt.2 = m} (chPacketCoverage n ξ ε c p) :=
  ⟨exists_sum_eq_chPacketCoverage, by
    rintro _ ⟨S, hS, hd, rfl⟩
    exact sum_le_chPacketCoverage hS hd⟩

/-- `M_c(p) = 0` when `Adm_c(p)` is empty. -/
theorem chPacketCoverage_eq_zero_of_chPackets_eq_empty (h : chPackets n ξ ε c p = ∅) :
    chPacketCoverage n ξ ε c p = 0 := by
  obtain ⟨S, hS, -, hsum⟩ := exists_sum_eq_chPacketCoverage (n := n) (ξ := ξ) (ε := ε)
    (c := c) (p := p)
  rw [h, Finset.subset_empty] at hS
  simp [← hsum, hS]

/-- `M_c(p) = 0` when `c ≤ 3`. -/
theorem chPacketCoverage_eq_zero_of_le (hc : c ≤ 3) : chPacketCoverage n ξ ε c p = 0 :=
  chPacketCoverage_eq_zero_of_chPackets_eq_empty (chPackets_eq_empty_of_le hc)

/-- `M_c(p) = 0` when `j(p) > ⌊n/2⌋`. -/
theorem chPacketCoverage_eq_zero_of_lt_bkJ (hp : ((n / 2 : ℕ) : ℤ) < bkJ p) :
    chPacketCoverage n ξ ε c p = 0 :=
  chPacketCoverage_eq_zero_of_chPackets_eq_empty (chPackets_eq_empty_of_lt_bkJ hp)

end CollatzPosDens
