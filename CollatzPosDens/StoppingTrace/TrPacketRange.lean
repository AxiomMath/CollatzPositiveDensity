/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrPacketDeficit
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

/-!
# The range of the packet deficit

Every entry `U_{s,t}` of the packet envelope table lies in `[1/2, 1]`. Consequently, by downward
induction on `i`, the packet values satisfy `0 ≤ F_{c,o}(i) ≤ (c - 1 - i) / 2`: each admissible
jump of length `t` contributes `t (1 - U_{o-i,t}) ∈ [0, t/2]`. Dividing by `c - 1` at `i = 0`
gives `0 ≤ δ^{pk}_{c,o} ≤ 1/2`.

## Main results

* `CollatzPosDens.one_half_le_chPacketTable`: `1/2 ≤ U_{s,t}` on `T_U`.
* `CollatzPosDens.trPacketValue_nonneg`, `CollatzPosDens.trPacketValue_le`:
  `0 ≤ F_{c,o}(i) ≤ (c - 1 - i) / 2`.
* `CollatzPosDens.trPacketDeficit_mem_Icc`: `0 ≤ δ^{pk}_{c,o} ≤ 1/2`.

## Implementation notes

The bounds hold for all natural numbers `c, o`, not only in the range `3 ≤ c ≤ 16`,
`1 ≤ o ≤ c`: for `c ≤ 1` the deficit is `0`. The subtraction `c - 1 - i` is
truncated, which matches the definition of `F_{c,o}(i) = 0` for `i ≥ c - 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Every entry of the packet envelope table on `T_U` is at least `1/2`. -/
theorem one_half_le_chPacketTable {s t : ℕ} (h : (s, t) ∈ chPacketTableDomain) :
    1 / 2 ≤ chPacketTable s t := by
  simp only [chPacketTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> norm_num [chPacketTable]

/-- Past the last position the packet value vanishes: `F_{c,o}(i) = 0` for `c - 1 ≤ i`. -/
theorem trPacketValue_of_le {c i : ℕ} (o : ℕ) (h : c - 1 ≤ i) : trPacketValue c o i = 0 := by
  rw [trPacketValue, Nat.sub_eq_zero_of_le h]
  rfl

/-- The packet values are bounded: `0 ≤ F_{c,o}(i) ≤ (c - 1 - i) / 2`. -/
theorem trPacketValue_mem_Icc (c o i : ℕ) :
    trPacketValue c o i ∈ Set.Icc 0 (((c - 1 - i : ℕ) : ℚ) / 2) := by
  induction h : c - 1 - i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    subst h
    rcases le_or_gt (c - 1) i with hi | hi
    · rw [trPacketValue_of_le o hi, Nat.sub_eq_zero_of_le hi]
      simp
    have h1 := ih (c - 1 - (i + 1)) (by omega) (i + 1) rfl
    refine ⟨h1.1.trans (trPacketValue_succ_le c o hi), ?_⟩
    rcases trPacketValue_eq_or_exists c o hi with h | ⟨t, ht1, ht2, hT, h⟩
    · rw [h]
      refine h1.2.trans ?_
      gcongr
      omega
    · rw [h]
      have h2 := (ih (c - 1 - (i + t)) (by omega) (i + t) rfl).2
      have hU := one_half_le_chPacketTable hT
      have hcast : ((c - 1 - i : ℕ) : ℚ) = (t : ℚ) + ((c - 1 - (i + t) : ℕ) : ℚ) := by
        rw [← Nat.cast_add]; congr 1; omega
      rw [hcast]
      have : (t : ℚ) * (1 - chPacketTable (o - i) t) ≤ t / 2 := by
        have : (0 : ℚ) ≤ t := t.cast_nonneg
        nlinarith
      linarith

/-- The packet values are nonnegative. -/
theorem trPacketValue_nonneg (c o i : ℕ) : 0 ≤ trPacketValue c o i :=
  (trPacketValue_mem_Icc c o i).1

/-- The packet values satisfy `F_{c,o}(i) ≤ (c - 1 - i) / 2`. -/
theorem trPacketValue_le (c o i : ℕ) :
    trPacketValue c o i ≤ ((c - 1 - i : ℕ) : ℚ) / 2 :=
  (trPacketValue_mem_Icc c o i).2

/-- The packet deficit lies in `[0, 1/2]`: `0 ≤ δ^{pk}_{c,o} ≤ 1/2`. This holds for all
`c, o`, in particular for `3 ≤ c ≤ 16`, `1 ≤ o ≤ c`. -/
@[collatz_pos_dens "lem_tr_packet_range"]
theorem trPacketDeficit_mem_Icc (c o : ℕ) : trPacketDeficit c o ∈ Set.Icc 0 (1 / 2) := by
  rcases le_or_gt c 1 with hc | hc
  · rw [trPacketDeficit, trPacketValue_of_le o (by omega)]
    simp
  have hpos : (0 : ℚ) < (c : ℚ) - 1 := by
    have : (1 : ℚ) < c := by exact_mod_cast hc
    linarith
  have hF := trPacketValue_le c o 0
  have hcast : ((c - 1 - 0 : ℕ) : ℚ) = (c : ℚ) - 1 := by
    rw [Nat.sub_zero, Nat.cast_sub hc.le, Nat.cast_one]
  rw [hcast] at hF
  rw [trPacketDeficit]
  refine ⟨div_nonneg (trPacketValue_nonneg c o 0) hpos.le, ?_⟩
  rw [div_le_iff₀ hpos]
  linarith

end CollatzPosDens
