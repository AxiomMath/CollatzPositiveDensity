/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrFirstStopPrefix
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrSublist
public import CollatzPosDens.StoppingTrace.TrTrace
public import CollatzPosDens.StoppingTrace.TrNoLateHit

/-!
# Second stops from a black origin are entry lists

Let `v ∈ 𝒫` be black, `N ∈ ℕ` with `j(v) + N > J`, where `J = ⌊n/2⌋`, let `β ∈ 𝔅^N` be live and
let `x = (x_t(v, β))_{t ∈ ℕ}` be its path from `v`. Since `x_0 = v` is black and
`1 ≤ j(v) ≤ J`, the first stopping time is `τ_1(x) = 0`, and a time `0 < t < J` is a hit of `x`
after `0` exactly when `x_t` is black with `l(x_t) > l_*(v)`. Because the path of the prefix
`β_{[1,q]}` agrees with that of `β` up to time `q`, and a black point `x_q` forces
`j(v) + q ≤ J < j(v) + N` (every black point `y` has `j(y) ≤ J`), the second stopping time is
read off the prefix: `ν(x) ≥ 2` and `τ_2(x) = q` hold together iff `1 ≤ q ≤ N` and
`β_{[1,q]} ∈ 𝓔(v)`.

## Main results

* `CollatzPosDens.trStopTime_two_eq_some_iff_trSublist_mem_trEntryWords`: the
  characterisation of the second stopping time by entry lists.

## Implementation notes

The condition `v ∈ 𝒫` (`1 ≤ j(v)`) is not part of `BkBlack`, so it is an explicit hypothesis. It
is needed: it gives `J ≥ 1`, without which `ν(x) = 0`. The list `β ∈ 𝔅^N` is a
`List (List ℤ × ℤ)` with `N = β.length` and every closing letter in `{4, 5}`, and `ε` is an
arbitrary colour scale.

## References

* [Mazur, *Collatz positive density*], §9.2.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}

/-- **Second stops from a black origin are entry lists.** Let `v ∈ 𝒫` be black, let `β ∈ 𝔅^N`
be live with `j(v) + N > ⌊n/2⌋`, and let `x = (x_t(v, β))_t`. Then `ν(x) ≥ 2` and `τ_2(x) = q`
hold together iff `1 ≤ q ≤ N` and `β_{[1,q]} ∈ 𝓔(v)`. -/
@[collatz_pos_dens "lem_tr_entry_prefix"]
theorem trStopTime_two_eq_some_iff_trSublist_mem_trEntryWords {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hvb : BkBlack n ξ ε v) (β : List (List ℤ × ℤ)) (hβ : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ))
    (hlive : TrLive β) (hN : ((n / 2 : ℕ) : ℤ) < bkJ v + β.length) (q : ℕ) :
    (2 ≤ trNu n ξ ε (trPath v β) ∧ trStopTime n ξ ε (trPath v β) 2 = some q) ↔
      1 ≤ q ∧ q ≤ β.length ∧ trSublist β 1 q ∈ trEntryWords n ξ ε v := by
  have hv1 : 1 ≤ bkJ v := hv
  have hvJ := hvb.bkJ_le
  have hJ : 0 < n / 2 := by omega
  have hτ1 : trStopTime n ξ ε (trPath v β) 1 = some 0 := by
    rw [trStopTime_one_eq_some_iff]
    exact ⟨hJ, by simpa [isTrHit_iff] using hvb, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
  have hlenq : ∀ {q : ℕ}, q ≤ β.length → (trSublist β 1 q).length = q :=
    fun hq => by simp [hq]
  have hτ2 : trStopTime n ξ ε (trPath v β) 2 = some q ↔
      q < n / 2 ∧ (0 < q ∧ IsTrHitAfter n ξ ε (trPath v β) 0 q) ∧
        ∀ s < q, ¬(0 < s ∧ IsTrHitAfter n ξ ε (trPath v β) 0 s) := by
    rw [trStopTime_succ_succ_eq_some_iff]
    refine ⟨fun ⟨t', ht', h⟩ => ?_, fun h => ⟨0, hτ1, h⟩⟩
    obtain rfl := Option.some_inj.1 (hτ1.symm.trans ht')
    exact h
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨hqJ, ⟨hq0, hhit⟩, hmin⟩ := hτ2.1 h
    have hlate := bkJ_add_le_of_bkJ_trPath_le v β hN hhit.1.bkJ_le
    have hqN : q ≤ β.length := by omega
    refine ⟨hq0, hqN, ?_⟩
    rw [mem_trEntryWords, hlenq hqN]
    refine ⟨fun b hb => hβ b (mem_of_mem_trSublist hb), hlive.sublist (trSublist_sublist _ _ _),
      hq0, ?_, fun t ht1 htq h => hmin t htq ⟨ht1, ?_⟩⟩
    · rw [trPath_trSublist_one_of_le v hqN le_rfl]
      simpa [isTrHitAfter_iff] using hhit
    · rw [trPath_trSublist_one_of_le v hqN htq.le] at h
      simpa [isTrHitAfter_iff] using h
  · rintro ⟨hq1, hqN, hu⟩
    rw [mem_trEntryWords, hlenq hqN] at hu
    obtain ⟨-, -, -, hhit, hnot⟩ := hu
    rw [trPath_trSublist_one_of_le v hqN le_rfl] at hhit
    have hlate := bkJ_add_le_of_bkJ_trPath_le v β hN hhit.1.bkJ_le
    have h2 : trStopTime n ξ ε (trPath v β) 2 = some q := by
      refine hτ2.2 ⟨by omega, ⟨hq1, by simpa [isTrHitAfter_iff] using hhit⟩, ?_⟩
      rintro s hs ⟨hs0, hs'⟩
      apply hnot s hs0 hs
      rw [trPath_trSublist_one_of_le v hqN hs.le]
      simpa [isTrHitAfter_iff] using hs'
    exact ⟨(isSome_trStopTime_iff.1 (by simp [h2])).2, h2⟩

end CollatzPosDens
