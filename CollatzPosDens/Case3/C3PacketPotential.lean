/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Case3.C3NarrowDeficit
public import Mathlib.Data.Finset.Max

/-!
# Packet deficits via a potential

This file computes the maximal packet deficit `a_{c,o}` (`CollatzPosDens.c3PacketDeficit`)
exactly, for `3 ≤ c ≤ 16` and `1 ≤ o ≤ c`.

The maximal packet deficit `a_{c,o}` is computed by dynamic programming. Put `n = c - 1` and, for
`0 ≤ i ≤ n`, let `F(i)` be the maximal weight of a packet family all of whose pairs `(i',t)` have
`i' ≥ i`. Then `F(n) = 0` and, for `i < n`,
`F(i) = max ({F(i+1)} ∪ {t (1 - U'_{o-i,t}) + F(i+t) : i + t ≤ n, (o - i, t) ∈ T'})`,
and `a_{c,o} = F(0)`. The upper bound `a_{c,o} ≤ F(0)` holds for any *potential* `φ` that is
nonnegative, nonincreasing, and dominates every packet step (`c3PacketDeficit_le_of_potential`):
an optimal family is peeled at its pair of least start. The lower bound is witnessed by the
family the recursion records.

## Main definitions

* `CollatzPosDens.c3PacketTable c o k`: the recursion's table `[(F(n-k), K_{n-k}), …, (F(n), ∅)]`,
  each value paired with a packet family attaining it.
* `CollatzPosDens.c3PacketPotential c o i`: the value `F(i)`.
* `CollatzPosDens.C3PacketCert c o`: the finite conditions certifying `a_{c,o} = F(0)`.
* `CollatzPosDens.c3PotN c o i`: the value `F(i)` scaled by `1024000000`, in natural numbers.

## Main results

* `CollatzPosDens.c3PacketDeficit_le_of_potential`: a potential bounds the maximal packet
  deficit.
* `CollatzPosDens.c3PacketPotential_eq_c3PotN`: `F(i) = c3PotN c o i / 1024000000`.
* `CollatzPosDens.c3PacketDeficit_eq_c3PacketPotential`: `a_{c,o} = F(0)` for `3 ≤ c ≤ 16`,
  `1 ≤ o ≤ c`.

## Implementation notes

The `133` values `a_{c,o}` are certified by kernel evaluation (`decide +kernel`) of the recursion,
of the potential conditions, and of the witnessing families, one evaluation for each `c`. The
values `F(i)` are multiples of `1/1024000000` (`1024000000 = 2^16 · 5^6`), so the kernel evaluates
them in natural numbers, through `CollatzPosDens.c3PacketTableN`, the recursion scaled by
`1024000000` (`CollatzPosDens.c3PacketTableN_spec`), and checks the list conditions
`CollatzPosDens.C3PacketCertN`, which imply `CollatzPosDens.C3PacketCert`
(`CollatzPosDens.C3PacketCertN.cert`), rather than computing in rational arithmetic.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-! ### A potential bounds the maximal packet deficit -/

section Potential

variable {c o : ℤ} {φ : ℤ → ℚ}

private theorem two_le_of_mem_c3PacketCandidates {p : ℤ × ℤ} (hp : p ∈ c3PacketCandidates c o) :
    2 ≤ p.2 :=
  (mem_c3NarrowTableDomain_bounds (mem_c3PacketCandidates.1 hp).2.2).2.2.1

private theorem potential_antitone
    (hmono : ∀ i, 0 ≤ i → i + 1 ≤ c - 1 → φ (i + 1) ≤ φ i) :
    ∀ i j, 0 ≤ i → i ≤ j → j ≤ c - 1 → φ j ≤ φ i := by
  intro i j hi hij hj
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = i + k := ⟨(j - i).toNat, by omega⟩
  clear hij
  induction k with
  | zero => simp
  | succ k ih =>
    push_cast at hj ⊢
    rw [← add_assoc]
    exact (hmono (i + k) (by omega) (by omega)).trans (ih (by omega))

/-- If `φ` is nonnegative and nonincreasing on `[0, c - 1]`, and
`t (1 - U'_{o-i,t}) + φ (i + t) ≤ φ i` for every candidate pair `(i,t)`, then every packet family
whose pairs start at indices `≥ i` has weight at most `φ i`. -/
private theorem c3PacketWeight_le_potential (hnn : ∀ i, 0 ≤ i → i ≤ c - 1 → 0 ≤ φ i)
    (hmono : ∀ i, 0 ≤ i → i + 1 ≤ c - 1 → φ (i + 1) ≤ φ i)
    (hstep : ∀ p ∈ c3PacketCandidates c o,
      (p.2 : ℚ) * (1 - c3NarrowTable (o - p.1) p.2) + φ (p.1 + p.2) ≤ φ p.1) :
    ∀ K : Finset (ℤ × ℤ), IsC3PacketFamily c o K → ∀ i, 0 ≤ i → i ≤ c - 1 →
      (∀ p ∈ K, i ≤ p.1) → c3PacketWeight o K ≤ φ i := by
  intro K
  induction K using Finset.strongInduction with
  | H K ih =>
  intro hK i hi0 hi hstart
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simpa using hnn i hi0 hi
  obtain ⟨p, hp, hmin⟩ := K.exists_min_image Prod.fst hne
  have hpc := hK.subset_c3PacketCandidates hp
  have hp2 := two_le_of_mem_c3PacketCandidates hpc
  obtain ⟨hp0, hpn, -⟩ := mem_c3PacketCandidates.1 hpc
  have hK' : IsC3PacketFamily c o (K.erase p) :=
    ⟨fun q hq => hK.1 q (Finset.mem_of_mem_erase hq),
      fun q hq r hr => hK.2 q (Finset.mem_of_mem_erase hq) r (Finset.mem_of_mem_erase hr)⟩
  have hstart' : ∀ q ∈ K.erase p, p.1 + p.2 ≤ q.1 := by
    intro q hq
    obtain ⟨hqp, hqK⟩ := Finset.mem_erase.1 hq
    have hq2 := two_le_of_mem_c3PacketCandidates (hK.subset_c3PacketCandidates hqK)
    have hd := hK.2 q hqK p hp hqp
    by_contra hlt
    have h1 : q.1 ∈ Finset.Ico q.1 (q.1 + q.2) := Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    have h2 : q.1 ∈ Finset.Ico p.1 (p.1 + p.2) :=
      Finset.mem_Ico.2 ⟨hmin q hqK, by omega⟩
    exact Finset.disjoint_left.1 hd h1 h2
  have hrec := ih (K.erase p) (Finset.erase_ssubset hp) hK' (p.1 + p.2) (by omega) hpn hstart'
  have hsplit : c3PacketWeight o K =
      (p.2 : ℚ) * (1 - c3NarrowTable (o - p.1) p.2) + c3PacketWeight o (K.erase p) := by
    unfold c3PacketWeight
    rw [← Finset.add_sum_erase K _ hp]
  rw [hsplit]
  calc _ ≤ (p.2 : ℚ) * (1 - c3NarrowTable (o - p.1) p.2) + φ (p.1 + p.2) := by linarith
    _ ≤ φ p.1 := hstep p hpc
    _ ≤ φ i := potential_antitone hmono i p.1 hi0 (hstart p hp) (by omega)

/-- A *potential* bounds the maximal packet deficit: if `φ` is nonnegative and nonincreasing on
`[0, c - 1]` and `t (1 - U'_{o-i,t}) + φ (i + t) ≤ φ i` for every candidate pair `(i,t)`, then
`a_{c,o} ≤ φ 0`. -/
theorem c3PacketDeficit_le_of_potential (hc : 1 ≤ c)
    (hnn : ∀ i, 0 ≤ i → i ≤ c - 1 → 0 ≤ φ i)
    (hmono : ∀ i, 0 ≤ i → i + 1 ≤ c - 1 → φ (i + 1) ≤ φ i)
    (hstep : ∀ p ∈ c3PacketCandidates c o,
      (p.2 : ℚ) * (1 - c3NarrowTable (o - p.1) p.2) + φ (p.1 + p.2) ≤ φ p.1) :
    c3PacketDeficit c o ≤ φ 0 :=
  c3PacketDeficit_le_iff.2 fun K hK =>
    c3PacketWeight_le_potential hnn hmono hstep K hK 0 le_rfl (by omega) fun p hp =>
      (mem_c3PacketCandidates.1 (hK.subset_c3PacketCandidates hp)).1

end Potential

/-! ### The recursion -/

/-- The rows `t ↦ U'_{s,t}` of the narrow packet envelope table, `0 ≤ s ≤ 8`, with `none` off
`T'`. -/
def c3NarrowRows : List (List (Option ℚ)) :=
  [[],
   [none, none, some (1 / 2 ^ 16), some (333340 / 1000000), some (500010 / 1000000)],
   [none, none, some (707108 / 1000000), some (333337 / 1000000), some (353560 / 1000000)],
   [none, none, some (923880 / 1000000), some (577352 / 1000000), some (461943 / 1000000)],
   [none, none, some (980786 / 1000000), some (883638 / 1000000), some (604555 / 1000000)],
   [none, none, some (995185 / 1000000), some (970239 / 1000000), some (867542 / 1000000)],
   [none, none, some (998796 / 1000000), some (992518 / 1000000), some (965743 / 1000000),
     some (864601 / 1000000)],
   [none, none, none, none, none, none, some (868067 / 1000000)],
   [none, none, none, none, none, none, none, some (874299 / 1000000)]]

/-- The table of the packet recursion for `(c,o)`, with `n = c - 1`: `c3PacketTable c o k` is the
list `[(F(n-k), K_{n-k}), …, (F(n), K_n)]`, where `F(i)` is the recursion's value at `i` and
`K_i` a family of pairs attaining it. A pair `(i,t)` is used when `(o - i, t) ∈ T'` and
`i + t ≤ n`; as `t ≤ 7` on `T'`, only `t ∈ {2, …, 7}` is tried. The entries `U'_{o-i,t}` are read
from the rows `CollatzPosDens.c3NarrowRows`; the recursion is only a candidate, certified by
`CollatzPosDens.C3PacketCert`. -/
def c3PacketTable (c o : ℤ) : ℕ → List (ℚ × List (ℤ × ℤ))
  | 0 => [(0, [])]
  | k + 1 =>
    let L := c3PacketTable c o k
    let i : ℤ := c - 1 - (k + 1)
    let row := c3NarrowRows.getD (o - i).toNat []
    (List.range' 2 6).foldl
      (fun acc (t : ℕ) =>
        match row.getD t none with
        | some U =>
          if t ≤ k + 1 then
            let e := L.getD (t - 1) (0, [])
            let v := (t : ℚ) * (1 - U) + e.1
            if acc.1 < v then (v, (i, (t : ℤ)) :: e.2) else acc
          else acc
        | none => acc)
      (L.headD (0, [])) :: L

/-- The recursion's entry `(F(i), K_i)` at index `i`, for `0 ≤ i ≤ c - 1`. -/
def c3PacketEntry (c o i : ℤ) : ℚ × List (ℤ × ℤ) :=
  (c3PacketTable c o (c - 1).toNat).getD i.toNat (0, [])

/-- The recursion's value `F(i)`: the maximal weight of a packet family for `(c,o)` all of whose
pairs start at indices `≥ i`. -/
def c3PacketPotential (c o i : ℤ) : ℚ :=
  (c3PacketEntry c o i).1

/-- The finite conditions certifying `a_{c,o} = F(0)`: `F` is a potential, and the recorded
family `K_0` is a packet family of weight `F(0)`. -/
def C3PacketCert (c o : ℤ) : Prop :=
  (∀ i ∈ Finset.Icc 0 (c - 1), 0 ≤ c3PacketPotential c o i) ∧
    (∀ i ∈ Finset.Ico 0 (c - 1), c3PacketPotential c o (i + 1) ≤ c3PacketPotential c o i) ∧
    (∀ p ∈ c3PacketCandidates c o,
      (p.2 : ℚ) * (1 - c3NarrowTable (o - p.1) p.2) + c3PacketPotential c o (p.1 + p.2) ≤
        c3PacketPotential c o p.1) ∧
    IsC3PacketFamily c o (c3PacketEntry c o 0).2.toFinset ∧
    c3PacketWeight o (c3PacketEntry c o 0).2.toFinset = c3PacketPotential c o 0

/-- The conditions `CollatzPosDens.C3PacketCert c o` are decidable. -/
instance (c o : ℤ) : Decidable (C3PacketCert c o) := by
  unfold C3PacketCert; infer_instance

/-- If the certificate `CollatzPosDens.C3PacketCert c o` holds and `1 ≤ c`, then
`a_{c,o} = F(0)`. -/
theorem c3PacketDeficit_eq_of_cert {c o : ℤ} (hc : 1 ≤ c) (h : C3PacketCert c o) :
    c3PacketDeficit c o = c3PacketPotential c o 0 := by
  obtain ⟨hnn, hmono, hstep, hfam, hw⟩ := h
  refine le_antisymm (c3PacketDeficit_le_of_potential hc ?_ ?_ hstep) ?_
  · exact fun i h0 h1 => hnn i (Finset.mem_Icc.2 ⟨h0, h1⟩)
  · exact fun i h0 h1 => hmono i (Finset.mem_Ico.2 ⟨h0, by omega⟩)
  · exact hw ▸ c3PacketWeight_le_c3PacketDeficit hfam

/-! ### Evaluation in natural numbers

The values `F(i)` are multiples of `1/1024000000`, so the certificate is evaluated by the kernel
in natural numbers, through a copy of the recursion scaled by `1024000000`. -/

/-- The rows `t ↦ 1024000000 (1 - U'_{s,t})` of the narrow packet envelope table, `0 ≤ s ≤ 8`,
with `none` off `T'`; `1024000000 = 2^16 · 5^6` is the least common denominator of the gaps
`1 - U'_{s,t}`. -/
def c3NarrowGapRowsN : List (List (Option ℕ)) :=
  [[],
   [none, none, some 1023984375, some 682659840, some 511989760],
   [none, none, some 299921408, some 682662912, some 661954560],
   [none, none, some 77946880, some 432791552, some 550970368],
   [none, none, some 19675136, some 119154688, some 404935680],
   [none, none, some 4930560, some 30475264, some 135636992],
   [none, none, some 1232896, some 7661568, some 35079168, some 138648576],
   [none, none, none, none, none, none, some 135099392],
   [none, none, none, none, none, none, none, some 128717824]]

/-- The rows of `U'` are recovered from the scaled gaps. -/
theorem c3NarrowRows_eq_map :
    c3NarrowRows = c3NarrowGapRowsN.map
      (List.map (Option.map fun g : ℕ => 1 - (g : ℚ) / 1024000000)) := by
  simp only [c3NarrowRows, c3NarrowGapRowsN, List.map_cons, List.map_nil, Option.map_some,
    Option.map_none]
  norm_num

/-- `CollatzPosDens.c3PacketTable` on values scaled by `1024000000`, in natural numbers. -/
def c3PacketTableN (c o : ℤ) : ℕ → List (ℕ × List (ℤ × ℤ))
  | 0 => [(0, [])]
  | k + 1 =>
    let L := c3PacketTableN c o k
    let i : ℤ := c - 1 - (k + 1)
    let row := c3NarrowGapRowsN.getD (o - i).toNat []
    (List.range' 2 6).foldl
      (fun acc (t : ℕ) =>
        match row.getD t none with
        | some g =>
          if t ≤ k + 1 then
            let e := L.getD (t - 1) (0, [])
            let v := t * g + e.1
            if acc.1 < v then (v, (i, (t : ℤ)) :: e.2) else acc
          else acc
        | none => acc)
      (L.headD (0, [])) :: L

/-- Undo the scaling of an entry of `CollatzPosDens.c3PacketTableN`. -/
def c3ScaleEntry (e : ℕ × List (ℤ × ℤ)) : ℚ × List (ℤ × ℤ) := ((e.1 : ℚ) / 1024000000, e.2)

private theorem getD_map' {α β : Type*} (f : α → β) (l : List α) (n : ℕ) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

private theorem c3ScaleEntry_zero : c3ScaleEntry (0, []) = (0, []) := by simp [c3ScaleEntry]

/-- The natural-number table, rescaled, is the rational table. -/
theorem c3PacketTableN_spec (c o : ℤ) (k : ℕ) :
    (c3PacketTableN c o k).map c3ScaleEntry = c3PacketTable c o k := by
  induction k with
  | zero => simp [c3PacketTableN, c3PacketTable, c3ScaleEntry]
  | succ k ih =>
    rw [c3PacketTableN, c3PacketTable, ← ih, List.map_cons]
    congr 1
    have hrow : ∀ n t, (c3NarrowRows.getD n []).getD t none =
        ((c3NarrowGapRowsN.getD n []).getD t none).map fun g : ℕ => 1 - (g : ℚ) / 1024000000 := by
      intro n t
      rw [c3NarrowRows_eq_map, ← List.map_nil, getD_map', ← Option.map_none, getD_map']
    rw [← c3ScaleEntry_zero, List.headD_map]
    refine (List.foldl_hom c3ScaleEntry fun acc t => ?_).symm
    simp only [hrow, getD_map']
    generalize (c3NarrowGapRowsN.getD _ []).getD t none = r
    rcases r with _ | g
    · rfl
    · simp only [Option.map_some]
      generalize (c3PacketTableN c o k).getD (t - 1) (0, []) = e
      have hv : (t : ℚ) * (1 - (1 - (g : ℚ) / 1024000000)) + (c3ScaleEntry e).1 =
          (c3ScaleEntry (t * g + e.1, ((c - 1 - (↑k + 1) : ℤ), (t : ℤ)) :: e.2)).1 := by
        simp only [c3ScaleEntry, Nat.cast_add, Nat.cast_mul]
        rw [sub_sub_cancel, mul_div_assoc', add_div]
      have hlt : (c3ScaleEntry acc).1 <
          (c3ScaleEntry (t * g + e.1, ((c - 1 - (↑k + 1) : ℤ), (t : ℤ)) :: e.2)).1 ↔
            acc.1 < t * g + e.1 := by
        simp only [c3ScaleEntry]
        rw [div_lt_div_iff_of_pos_right (by norm_num)]
        exact_mod_cast Iff.rfl
      rw [hv]
      simp only [hlt]
      split_ifs <;> rfl

/-- The value `F(i)` scaled by `1024000000`. -/
def c3PotN (c o i : ℤ) : ℕ := ((c3PacketTableN c o (c - 1).toNat).getD i.toNat (0, [])).1

/-- The family `K_0` recorded by the recursion, computed by `CollatzPosDens.c3PacketTableN`. -/
def c3FamN (c o : ℤ) : List (ℤ × ℤ) := ((c3PacketTableN c o (c - 1).toNat).getD 0 (0, [])).2

/-- The recursion's entries, read from the natural-number table. -/
theorem c3PacketEntry_eq (c o i : ℤ) :
    c3PacketEntry c o i =
      c3ScaleEntry ((c3PacketTableN c o (c - 1).toNat).getD i.toNat (0, [])) := by
  rw [c3PacketEntry, ← c3PacketTableN_spec, ← c3ScaleEntry_zero, getD_map']

/-- `F(i) = c3PotN c o i / 1024000000`. -/
theorem c3PacketPotential_eq_c3PotN (c o i : ℤ) :
    c3PacketPotential c o i = (c3PotN c o i : ℚ) / 1024000000 := by
  rw [c3PacketPotential, c3PacketEntry_eq]; rfl

/-- The family `K_0`, read from the natural-number table. -/
theorem c3PacketEntry_zero_snd (c o : ℤ) : (c3PacketEntry c o 0).2 = c3FamN c o := by
  rw [c3PacketEntry_eq]; rfl

/-- `1024000000 (1 - U'_{s,t})` on `T'` (and `0` off it). -/
def c3GapN (s t : ℤ) : ℕ := ((c3NarrowGapRowsN.getD s.toNat []).getD t.toNat none).getD 0

/-- On `T'`, `c3GapN s t / 1024000000 = 1 - U'_{s,t}`. -/
theorem c3GapN_spec {s t : ℤ} (h : (s, t) ∈ c3NarrowTableDomain) :
    (c3GapN s t : ℚ) / 1024000000 = 1 - c3NarrowTable s t := by
  simp only [c3NarrowTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> rw [c3NarrowTable, c3GapN.eq_1] <;> norm_num [c3NarrowGapRowsN]

/-- The pairs of `T'`, as a list. -/
def c3NarrowDomainList : List (ℤ × ℤ) :=
  [(1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (3, 4), (4, 2), (4, 3), (4, 4),
   (5, 2), (5, 3), (5, 4), (6, 2), (6, 3), (6, 4), (6, 5), (7, 6), (8, 7)]

/-- The list `CollatzPosDens.c3NarrowDomainList` has the members of `T'`. -/
theorem mem_c3NarrowDomainList {p : ℤ × ℤ} :
    p ∈ c3NarrowDomainList ↔ p ∈ c3NarrowTableDomain := by
  simp only [c3NarrowDomainList, c3NarrowTableDomain, List.mem_cons, List.not_mem_nil,
    Finset.mem_insert, Finset.mem_singleton, or_false]

/-- The conditions of `CollatzPosDens.C3PacketCert` in natural-number arithmetic, quantified over
lists (the nonnegativity of the potential being automatic). -/
def C3PacketCertN (c o : ℤ) : Prop :=
  (∀ i ∈ List.range (c - 1).toNat, c3PotN c o ((i + 1 : ℕ) : ℤ) ≤ c3PotN c o (i : ℤ)) ∧
    (∀ st ∈ c3NarrowDomainList, 0 ≤ o - st.1 → o - st.1 + st.2 ≤ c - 1 →
      st.2.toNat * c3GapN st.1 st.2 + c3PotN c o (o - st.1 + st.2) ≤ c3PotN c o (o - st.1)) ∧
    (∀ p ∈ c3FamN c o, 0 ≤ p.1 ∧ p.1 + p.2 ≤ c - 1 ∧ (o - p.1, p.2) ∈ c3NarrowDomainList) ∧
    (∀ p ∈ c3FamN c o, ∀ q ∈ c3FamN c o, p ≠ q → p.1 + p.2 ≤ q.1 ∨ q.1 + q.2 ≤ p.1) ∧
    (c3FamN c o).Nodup ∧
    ((c3FamN c o).map fun p => p.2.toNat * c3GapN (o - p.1) p.2).sum = c3PotN c o 0

/-- The conditions `CollatzPosDens.C3PacketCertN c o` are decidable. -/
instance (c o : ℤ) : Decidable (C3PacketCertN c o) := by
  unfold C3PacketCertN; infer_instance

private theorem term_eq {o : ℤ} {p : ℤ × ℤ} (hT : (o - p.1, p.2) ∈ c3NarrowTableDomain) :
    (p.2 : ℚ) * (1 - c3NarrowTable (o - p.1) p.2) =
      ((p.2.toNat * c3GapN (o - p.1) p.2 : ℕ) : ℚ) / 1024000000 := by
  have h2 := (mem_c3NarrowTableDomain_bounds hT).2.2.1
  have ht : ((p.2.toNat : ℕ) : ℚ) = (p.2 : ℚ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
  rw [← c3GapN_spec hT, Nat.cast_mul, mul_div_assoc, ht]

private theorem sum_cast_div {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ∑ i ∈ s, (f i : ℚ) / 1024000000 = ((∑ i ∈ s, f i : ℕ) : ℚ) / 1024000000 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Nat.cast_add, add_div]

/-- The natural-number conditions imply `CollatzPosDens.C3PacketCert`. -/
theorem C3PacketCertN.cert {c o : ℤ} (h : C3PacketCertN c o) : C3PacketCert c o := by
  obtain ⟨hmono, hstep, hmem, hdisj, hnodup, hw⟩ := h
  have hfam : IsC3PacketFamily c o (c3FamN c o).toFinset := by
    refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
    · obtain ⟨h0, h1, h2⟩ := hmem p (List.mem_toFinset.1 hp)
      exact ⟨h0, h1, mem_c3NarrowDomainList.1 h2⟩
    · have h := hdisj p (List.mem_toFinset.1 hp) q (List.mem_toFinset.1 hq) hpq
      refine Finset.disjoint_left.2 fun x hxp hxq => ?_
      rw [Finset.mem_Ico] at hxp hxq
      omega
  simp only [C3PacketCert, c3PacketPotential_eq_c3PotN, c3PacketEntry_zero_snd]
  refine ⟨fun i _ => div_nonneg (Nat.cast_nonneg _) (by norm_num), fun i hi => ?_,
    fun p hp => ?_, hfam, ?_⟩
  · obtain ⟨hi0, hi1⟩ := Finset.mem_Ico.1 hi
    have h := hmono i.toNat (List.mem_range.2 (by omega))
    rw [Nat.cast_add, Int.toNat_of_nonneg hi0, Nat.cast_one] at h
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)
  · obtain ⟨h0, h1, hT⟩ := mem_c3PacketCandidates.1 hp
    have h := hstep _ (mem_c3NarrowDomainList.2 hT) (by simpa using h0) (by simpa using h1)
    simp only [sub_sub_cancel] at h
    rw [term_eq hT, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)
  · rw [c3PacketWeight, Finset.sum_congr rfl fun p hp => term_eq (hfam.1 p hp).2.2,
      sum_cast_div, List.sum_toFinset _ hnodup, hw]

/-- The certificates of a row `c`, from the natural-number conditions. -/
theorem c3PacketCert_of_forall_certN {c : ℤ}
    (h : ∀ o ∈ List.range' 1 c.toNat, C3PacketCertN c (o : ℤ)) :
    ∀ o ∈ Finset.Icc 1 c, C3PacketCert c o := by
  intro o ho
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ho
  have := h o.toNat (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  rw [Int.toNat_of_nonneg (by omega)] at this
  exact this.cert

private theorem c3PacketCert_3 : ∀ o ∈ Finset.Icc (1 : ℤ) 3, C3PacketCert 3 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_4 : ∀ o ∈ Finset.Icc (1 : ℤ) 4, C3PacketCert 4 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_5 : ∀ o ∈ Finset.Icc (1 : ℤ) 5, C3PacketCert 5 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_6 : ∀ o ∈ Finset.Icc (1 : ℤ) 6, C3PacketCert 6 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_7 : ∀ o ∈ Finset.Icc (1 : ℤ) 7, C3PacketCert 7 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_8 : ∀ o ∈ Finset.Icc (1 : ℤ) 8, C3PacketCert 8 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_9 : ∀ o ∈ Finset.Icc (1 : ℤ) 9, C3PacketCert 9 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_10 : ∀ o ∈ Finset.Icc (1 : ℤ) 10, C3PacketCert 10 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_11 : ∀ o ∈ Finset.Icc (1 : ℤ) 11, C3PacketCert 11 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_12 : ∀ o ∈ Finset.Icc (1 : ℤ) 12, C3PacketCert 12 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_13 : ∀ o ∈ Finset.Icc (1 : ℤ) 13, C3PacketCert 13 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_14 : ∀ o ∈ Finset.Icc (1 : ℤ) 14, C3PacketCert 14 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_15 : ∀ o ∈ Finset.Icc (1 : ℤ) 15, C3PacketCert 15 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

private theorem c3PacketCert_16 : ∀ o ∈ Finset.Icc (1 : ℤ) 16, C3PacketCert 16 o :=
  c3PacketCert_of_forall_certN (by decide +kernel)

/-- The certificates of all rows `3 ≤ c ≤ 16`, one kernel evaluation per row `c`. -/
theorem c3PacketCert_all :
    ∀ c ∈ Finset.Icc (3 : ℤ) 16, ∀ o ∈ Finset.Icc 1 c, C3PacketCert c o := by
  intro c hc
  obtain ⟨h3, h16⟩ := Finset.mem_Icc.1 hc
  have hc' : c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨
      c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 := by omega
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [c3PacketCert_3, c3PacketCert_4, c3PacketCert_5, c3PacketCert_6, c3PacketCert_7,
    c3PacketCert_8, c3PacketCert_9, c3PacketCert_10, c3PacketCert_11, c3PacketCert_12,
    c3PacketCert_13, c3PacketCert_14, c3PacketCert_15, c3PacketCert_16]

/-- For `3 ≤ c ≤ 16` and `1 ≤ o ≤ c`, the maximal packet deficit is the value `F(0)` of the
packet recursion. -/
theorem c3PacketDeficit_eq_c3PacketPotential {c o : ℤ} (hc : c ∈ Finset.Icc (3 : ℤ) 16)
    (ho : o ∈ Finset.Icc 1 c) : c3PacketDeficit c o = c3PacketPotential c o 0 :=
  c3PacketDeficit_eq_of_cert (by simp at hc; omega) (c3PacketCert_all c hc o ho)

end CollatzPosDens
