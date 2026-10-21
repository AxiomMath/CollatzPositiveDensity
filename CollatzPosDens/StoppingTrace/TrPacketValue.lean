/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPacketTable
public import Mathlib.Algebra.Order.Field.Basic

/-!
# The packet value recursion

For integers `c, o`, the packet values `F_{c,o}(i)`, `0 ≤ i ≤ c - 1`, are defined by downward
recursion on `i`: `F_{c,o}(c - 1) = 0`, and for `i < c - 1` the value `F_{c,o}(i)` is the largest
element of the finite set
`{F_{c,o}(i+1)} ∪ {t (1 - U_{o-i,t}) + F_{c,o}(i+t) : t ≥ 1, i + t ≤ c - 1, (o - i, t) ∈ T_U}`,
where `U` is the packet envelope table on its index set `T_U`.

## Main definitions

* `CollatzPosDens.trPacketValue c o i`: the packet value `F_{c,o}(i)`.
* `CollatzPosDens.pvN c o`: the packet value `F_{c,o}(0)` scaled by `10^6`, computed in natural
  numbers by `CollatzPosDens.pkListN`, a copy of the recursion.

## Main results

* `CollatzPosDens.trPacketValue_last`: `F_{c,o}(c - 1) = 0`.
* `CollatzPosDens.isGreatest_trPacketValue`: for `i < c - 1`, `F_{c,o}(i)` is the largest
  element of `{F_{c,o}(i+1)} ∪ {t (1 - U_{o-i,t}) + F_{c,o}(i+t)}` over admissible `t`.
* `CollatzPosDens.trPacketValue_succ_le`, `CollatzPosDens.trPacketValue_add_le`: the two
  families of lower bounds furnished by the recursion.
* `CollatzPosDens.trPacketValue_eq_pvN`: `F_{c,o}(0) = pvN c o / 10^6`.

## Implementation notes

The definition is computable and structurally recursive. Its values are multiples of `10^{-6}`,
so the kernel evaluates them through `CollatzPosDens.pkListN`, the same recursion in natural
numbers scaled by `10^6` (`CollatzPosDens.pkListN_spec`), rather than in rational arithmetic. The
list `trPacketValueList c o n` stores `[F_{c,o}(c-1-n), …, F_{c,o}(c-1)]`; each step prepends one
new value, computed from the list already built. The definition is made for all natural numbers
`c, o, i`, without the range restrictions `3 ≤ c ≤ 16`, `1 ≤ o ≤ c`. The difference `o - i` is
truncated subtraction: when `i ≥ o` it equals `0`, and `(0, t)` lies outside `T_U` just as a
nonpositive integer first coordinate does, so the set in the recursion is unchanged.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- One step of the packet value recursion at position `i`: given the list
`L = [F(i+1), …, F(c-1)]`, return the largest of `F(i+1)` and the values
`t (1 - U_{o-i,t}) + F(i+t)` over `1 ≤ t ≤ L.length` with `(o - i, t) ∈ T_U`. -/
def trPacketValueStep (o i : ℕ) (L : List ℚ) : ℚ :=
  (((List.range' 1 L.length).filter (fun t : ℕ => (o - i, t) ∈ chPacketTableDomain)).map
    (fun t : ℕ => (t : ℚ) * (1 - chPacketTable (o - i) t) + L.getD (t - 1) 0)).foldr max (L.headD 0)

/-- The list `[F_{c,o}(c-1-n), …, F_{c,o}(c-1)]` of the last `n + 1` packet values. -/
def trPacketValueList (c o : ℕ) : ℕ → List ℚ
  | 0 => [0]
  | n + 1 => trPacketValueStep o (c - 2 - n) (trPacketValueList c o n) :: trPacketValueList c o n

/-- The packet value `F_{c,o}(i)`, defined by downward recursion on `i` from
`F_{c,o}(c-1) = 0`: for `i < c - 1`, `F_{c,o}(i)` is the largest element of
`{F_{c,o}(i+1)} ∪ {t (1 - U_{o-i,t}) + F_{c,o}(i+t) : t ≥ 1, i + t ≤ c - 1, (o-i,t) ∈ T_U}`. -/
@[collatz_pos_dens "def_tr_packet_value"]
def trPacketValue (c o i : ℕ) : ℚ :=
  (trPacketValueList c o (c - 1 - i)).headD 0

/-- The list `trPacketValueList c o n` has length `n + 1`. -/
theorem length_trPacketValueList (c o n : ℕ) : (trPacketValueList c o n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trPacketValueList, ih]

/-- For `j ≤ m`, the `j`-th entry of `trPacketValueList c o m` is the head of
`trPacketValueList c o (m - j)`. -/
theorem getD_trPacketValueList (c o : ℕ) {m j : ℕ} (h : j ≤ m) :
    (trPacketValueList c o m).getD j 0 = (trPacketValueList c o (m - j)).headD 0 := by
  induction m generalizing j with
  | zero =>
    obtain rfl : j = 0 := by omega
    rfl
  | succ m ih =>
    rcases j with _ | j
    · cases h' : trPacketValueList c o (m + 1) <;> simp
    · rw [trPacketValueList, List.getD_cons_succ, ih (by omega)]
      congr 2
      omega

/-- The value at the last position vanishes: `F_{c,o}(c - 1) = 0`. -/
@[simp]
theorem trPacketValue_last (c o : ℕ) : trPacketValue c o (c - 1) = 0 := by
  simp [trPacketValue, trPacketValueList]

private theorem isGreatest_foldr_max (a : ℚ) (l : List ℚ) :
    IsGreatest {x | x = a ∨ x ∈ l} (l.foldr max a) := by
  induction l with
  | nil => simp [IsGreatest, upperBounds]
  | cons b l ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [List.foldr_cons, Set.mem_ofPred_eq, List.mem_cons]
      rcases le_total b (l.foldr max a) with hb | hb
      · rw [max_eq_right hb]
        rcases h1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rw [max_eq_left hb]
        exact Or.inr (Or.inl rfl)
    · intro x hx
      simp only [Set.mem_ofPred_eq, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact le_max_of_le_right (h2 (Or.inl rfl))
      · exact le_max_left _ _
      · exact le_max_of_le_right (h2 (Or.inr hx))

/-- For `i < c - 1`, `F_{c,o}(i)` is `trPacketValueStep` applied to the list
`[F_{c,o}(i+1), …, F_{c,o}(c-1)]`. -/
theorem trPacketValue_eq_step (c o : ℕ) {i : ℕ} (hi : i < c - 1) :
    trPacketValue c o i = trPacketValueStep o i (trPacketValueList c o (c - 2 - i)) := by
  have h : c - 1 - i = (c - 2 - i) + 1 := by omega
  rw [trPacketValue, h, trPacketValueList]
  simp only [List.headD_cons]
  congr 1
  omega

/-- For `i < c - 1`, `F_{c,o}(i)` is the largest element of
`{F_{c,o}(i+1)} ∪ {t (1 - U_{o-i,t}) + F_{c,o}(i+t) : t ≥ 1, i + t ≤ c - 1, (o-i,t) ∈ T_U}`. -/
theorem isGreatest_trPacketValue (c o : ℕ) {i : ℕ} (hi : i < c - 1) :
    IsGreatest ({trPacketValue c o (i + 1)} ∪
      {x | ∃ t : ℕ, 1 ≤ t ∧ i + t ≤ c - 1 ∧ (o - i, t) ∈ chPacketTableDomain ∧
        x = t * (1 - chPacketTable (o - i) t) + trPacketValue c o (i + t)})
      (trPacketValue c o i) := by
  rw [trPacketValue_eq_step c o hi, trPacketValueStep]
  set L := trPacketValueList c o (c - 2 - i) with hL
  have hlen : L.length = c - 1 - i := by rw [hL, length_trPacketValueList]; omega
  have hhead : L.headD 0 = trPacketValue c o (i + 1) := by
    rw [trPacketValue, hL]; congr 2; omega
  have hget : ∀ t, 1 ≤ t → i + t ≤ c - 1 → L.getD (t - 1) 0 = trPacketValue c o (i + t) := by
    intro t ht1 ht2
    rw [hL, getD_trPacketValueList c o (by omega), trPacketValue]
    congr 2
    omega
  convert isGreatest_foldr_max (L.headD 0) _ using 1
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_map,
    List.mem_filter, List.mem_range'_1, decide_eq_true_eq, hhead, hlen]
  constructor
  · rintro (h | ⟨t, ht1, ht2, hT, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ⟨⟨ht1, by omega⟩, hT⟩, by rw [hget t ht1 ht2]⟩
  · rintro (h | ⟨t, ⟨⟨ht1, ht2⟩, hT⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht1, by omega, hT, by rw [hget t ht1 (by omega)]⟩

/-- The recursion makes `F_{c,o}` weakly decreasing: `F_{c,o}(i+1) ≤ F_{c,o}(i)` for
`i < c - 1`. -/
theorem trPacketValue_succ_le (c o : ℕ) {i : ℕ} (hi : i < c - 1) :
    trPacketValue c o (i + 1) ≤ trPacketValue c o i :=
  (isGreatest_trPacketValue c o hi).2 (Or.inl rfl)

/-- Each admissible jump gives a lower bound:
`t (1 - U_{o-i,t}) + F_{c,o}(i+t) ≤ F_{c,o}(i)`. -/
theorem trPacketValue_add_le (c o : ℕ) {i t : ℕ} (ht1 : 1 ≤ t) (ht2 : i + t ≤ c - 1)
    (hT : (o - i, t) ∈ chPacketTableDomain) :
    t * (1 - chPacketTable (o - i) t) + trPacketValue c o (i + t) ≤ trPacketValue c o i := by
  have hi : i < c - 1 := by
    have := (mem_chPacketTableDomain_bounds hT).2
    omega
  exact (isGreatest_trPacketValue c o hi).2 (Or.inr ⟨t, ht1, ht2, hT, rfl⟩)

/-- For `i < c - 1`, `F_{c,o}(i)` is attained: it equals `F_{c,o}(i+1)` or one of the values
`t (1 - U_{o-i,t}) + F_{c,o}(i+t)` with `t` admissible. -/
theorem trPacketValue_eq_or_exists (c o : ℕ) {i : ℕ} (hi : i < c - 1) :
    trPacketValue c o i = trPacketValue c o (i + 1) ∨
      ∃ t : ℕ, 1 ≤ t ∧ i + t ≤ c - 1 ∧ (o - i, t) ∈ chPacketTableDomain ∧
        trPacketValue c o i = t * (1 - chPacketTable (o - i) t) + trPacketValue c o (i + t) :=
  (isGreatest_trPacketValue c o hi).1

/-! ### A fast evaluator for the packet values -/

/-- Membership in the index set `T_U` of the packet envelope table, by arithmetic. -/
def pkIn (s t : ℕ) : Bool :=
  (Nat.ble 1 s && Nat.ble s 6 && Nat.ble 2 t && Nat.ble t 4) || (s == 6 && t == 5) ||
    (s == 7 && t == 6) || (s == 8 && t == 7)

/-- `pkIn s t` holds exactly when `(s, t)` lies in the index set `T_U`. -/
theorem pkIn_iff (s t : ℕ) : pkIn s t = true ↔ (s, t) ∈ chPacketTableDomain := by
  constructor
  · intro h
    simp only [pkIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq] at h
    rcases h with ((⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
    · obtain rfl | rfl | rfl | rfl | rfl | rfl : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 := by
        omega
      all_goals obtain rfl | rfl | rfl : t = 2 ∨ t = 3 ∨ t = 4 := by omega
      all_goals decide
    all_goals decide
  · intro h
    simp only [chPacketTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;> rfl

/-- `10^6 (1 - U_{s,t})` on the index set `T_U` (and `0` off it). -/
def pkGap : ℕ → ℕ → ℕ
  | 1, 2 => 500000 | 1, 3 => 410000 | 1, 4 => 496000
  | 2, 2 => 133000 | 2, 3 => 421000 | 2, 4 => 374000
  | 3, 2 => 34070 | 3, 3 => 200000 | 3, 4 => 465000
  | 4, 2 => 8000 | 4, 3 => 52590 | 4, 4 => 225000
  | 5, 2 => 2140 | 5, 3 => 13280 | 5, 4 => 60370
  | 6, 2 => 535 | 6, 3 => 3328 | 6, 4 => 15318 | 6, 5 => 61000
  | 7, 6 => 60000 | 8, 7 => 57000 | _, _ => 0

/-- On the index set `T_U`, `pkGap s t / 10^6 = 1 - U_{s,t}`. -/
theorem pkGap_spec {s t : ℕ} (h : (s, t) ∈ chPacketTableDomain) :
    (pkGap s t : ℚ) / 10 ^ 6 = 1 - chPacketTable s t := by
  simp only [chPacketTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> rw [pkGap, chPacketTable] <;> norm_num

/-- `trPacketValueStep` on values scaled by `10^6`, in natural numbers. -/
def pkStepN (o i : ℕ) (L : List ℕ) : ℕ :=
  (((List.range' 1 L.length).filter (fun t : ℕ => pkIn (o - i) t)).map
    (fun t : ℕ => t * pkGap (o - i) t + L.getD (t - 1) 0)).foldr max (L.headD 0)

/-- `trPacketValueList` on values scaled by `10^6`, in natural numbers. -/
def pkListN (c o : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => pkStepN o (c - 2 - n) (pkListN c o n) :: pkListN c o n

/-- Dividing by `10^6` commutes with taking the maximum of a list of natural numbers. -/
theorem foldr_max_map_div (a : ℕ) (l : List ℕ) :
    (((l.foldr max a : ℕ) : ℚ) / 10 ^ 6) =
      (l.map fun x : ℕ => (x : ℚ) / 10 ^ 6).foldr max ((a : ℚ) / 10 ^ 6) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldr_cons, List.map_cons, ← ih, Nat.cast_max]
    exact (max_div_div_right (by positivity) _ _).symm

/-- `pkStepN` divided by `10^6` is `trPacketValueStep` on the list divided by `10^6`. -/
theorem pkStepN_spec (o i : ℕ) (L : List ℕ) :
    ((pkStepN o i L : ℕ) : ℚ) / 10 ^ 6 =
      trPacketValueStep o i (L.map fun x : ℕ => (x : ℚ) / 10 ^ 6) := by
  rw [pkStepN, trPacketValueStep, foldr_max_map_div, List.length_map, List.map_map]
  have hf : (List.range' 1 L.length).filter (fun t : ℕ => pkIn (o - i) t) =
      (List.range' 1 L.length).filter (fun t : ℕ => (o - i, t) ∈ chPacketTableDomain) :=
    List.filter_congr fun t _ => by
      rw [Bool.eq_iff_iff, pkIn_iff, decide_eq_true_iff]
  rw [hf]
  have hh : ((L.headD 0 : ℕ) : ℚ) / 10 ^ 6 = (L.map fun x : ℕ => (x : ℚ) / 10 ^ 6).headD 0 := by
    cases L <;> simp
  rw [hh]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [List.mem_filter, decide_eq_true_iff] at ht
  simp only [Function.comp, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [Nat.cast_add, add_div, Nat.cast_mul, mul_div_assoc, pkGap_spec ht.2]
  congr 1
  cases L[t - 1]? <;> simp

/-- `pkListN c o n` divided by `10^6` entrywise is `trPacketValueList c o n`. -/
theorem pkListN_spec (c o n : ℕ) :
    (pkListN c o n).map (fun x : ℕ => (x : ℚ) / 10 ^ 6) = trPacketValueList c o n := by
  induction n with
  | zero => simp [pkListN, trPacketValueList]
  | succ n ih =>
    simp only [pkListN, trPacketValueList, List.map_cons, pkStepN_spec, ih]

/-- The packet value `F_{c,o}(0)`, scaled by `10^6`. -/
def pvN (c o : ℕ) : ℕ := (pkListN c o (c - 1)).headD 0

/-- The packet value `F_{c,o}(0)` equals `pvN c o / 10^6`. -/
theorem trPacketValue_eq_pvN (c o : ℕ) : trPacketValue c o 0 = (pvN c o : ℚ) / 10 ^ 6 := by
  rw [trPacketValue, Nat.sub_zero, ← pkListN_spec, pvN]
  cases pkListN c o (c - 1) <;> simp

example : trPacketValue 3 1 0 = 1 := by
  rw [trPacketValue_eq_pvN, show pvN 3 1 = 10 ^ 6 by decide +kernel]
  norm_num

end CollatzPosDens
