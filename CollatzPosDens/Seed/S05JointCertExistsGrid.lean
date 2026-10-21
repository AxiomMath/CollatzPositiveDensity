/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Seed.S05OfflawGrid

/-!
# Packed tables and the tabulated offset grid

The certificates of the offset law are explicit tables of natural numbers that the kernel reads
at random positions. A list `l = (l_0, l_1, …)` of natural numbers below `2^w` is stored as the
single natural number `∑_i l_i 2^{w i}`, whose `w`-bit lanes are the entries; the entry at a
position `i` is then `⌊N / 2^{w i}⌋ mod 2^w`, one shift and one remainder of binary numbers.
Long tables are packed in blocks of `256` entries and kept as the list of the blocks, so that a
read touches one block only.

The numerators `n_j = 512 ξ_j` of the offset grid are tabulated in this form for `j < 6400`,
and the table agrees with `CollatzPosDens.offlawGridNum` for `j ≤ 6199`.

## Main definitions

* `CollatzPosDens.jointCertPack w l`: the entries of `l` as the `w`-bit lanes of one number.
* `CollatzPosDens.jointCertLane w N i`: the `i`-th `w`-bit lane of `N`.
* `CollatzPosDens.jointCertBlockLane w blocks i`: the entry at position `i` of a table stored
  as a list of packed blocks of `256` entries.
* `CollatzPosDens.jointCertGridTab j`: the tabulated grid numerator `n_j`.

## Main results

* `CollatzPosDens.jointCertGridTab_eq`: `jointCertGridTab j = offlawGridNum j` for `j < 6200`.

## Implementation notes

All loops are bare recursors on `ℕ` and `List`, and all arithmetic is the binary arithmetic of
`ℕ`, so that the kernel evaluates them directly.

## References

* [Mazur, *Collatz positive density*], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The entries of `l` as the `w`-bit lanes of one natural number, lane `i` holding `l_i`
(when every entry is below `2^w`). -/
def jointCertPack (w : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add x (Nat.shiftLeft ih w)) l

/-- The `i`-th `w`-bit lane `⌊N / 2^{w i}⌋ mod 2^w` of a natural number `N`. -/
def jointCertLane (w N i : ℕ) : ℕ :=
  Nat.mod (Nat.shiftRight N (Nat.mul w i)) (Nat.shiftLeft 1 w)

/-- The entry at position `i` of a list, and `0` past its end. -/
def jointCertNth (l : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun x _ ih i => Nat.casesOn (motive := fun _ => ℕ) i x fun j => ih j) l

/-- The entry at position `i` of a table stored as a list of blocks of `256` entries, each
block packed with the lane width `w`: lane `i mod 256` of the block `⌊i / 256⌋`. -/
def jointCertBlockLane (w : ℕ) (blocks : List ℕ) (i : ℕ) : ℕ :=
  jointCertLane w (jointCertNth blocks (Nat.div i 256)) (Nat.mod i 256)

/-- The block `b` of the grid table: the numerators `n_{256 b}, …, n_{256 b + 255}`. -/
def jointCertGridBlock (b : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [] (fun i l => offlawGridNum (256 * b + (255 - i)) :: l)
    256

/-- The grid numerators `n_0, …, n_6399` in `25` blocks of `256`, each packed with `64`-bit
lanes. -/
def jointCertGridBlocks : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) []
    (fun b l => jointCertPack 64 (jointCertGridBlock (24 - b)) :: l) 25

/-- The tabulated grid numerator `n_j` (for `j < 6400`). -/
def jointCertGridTab (j : ℕ) : ℕ :=
  jointCertBlockLane 64 jointCertGridBlocks j

/-- The check that the grid table agrees with `offlawGridNum` at the indices `j < n`. -/
def jointCertGridCheck (n : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => Nat.beq (jointCertGridTab j) (offlawGridNum j) && ih) n

/-- A passed check gives the agreement of the grid table at the checked indices. -/
theorem jointCertGridTab_eq_of_check {n : ℕ} (h : jointCertGridCheck n = true) {j : ℕ}
    (hj : j < n) : jointCertGridTab j = offlawGridNum j := by
  induction n with
  | zero => omega
  | succ n ih =>
    change (Nat.beq (jointCertGridTab n) (offlawGridNum n) && jointCertGridCheck n) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact ih h.2 hj
    · exact h.1

/-- The grid table passes the check at the indices `j < 6200`, by kernel evaluation. -/
theorem jointCertGridCheck_6200 : jointCertGridCheck 6200 = true := by
  decide +kernel

/-- The grid table agrees with the grid numerators: `jointCertGridTab j = n_j` for `j < 6200`. -/
theorem jointCertGridTab_eq {j : ℕ} (hj : j < 6200) : jointCertGridTab j = offlawGridNum j :=
  jointCertGridTab_eq_of_check jointCertGridCheck_6200 hj

end CollatzPosDens
