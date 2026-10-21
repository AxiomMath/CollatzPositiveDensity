/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Seed.S05JointCert
public import CollatzPosDens.Seed.S05JointCertExistsG
public import CollatzPosDens.Seed.S05JointCertExistsYData1
public import CollatzPosDens.Seed.S05JointCertExistsYData2
public import CollatzPosDens.Seed.S05JointCertExistsYData3
public import CollatzPosDens.Seed.S05JointCertExistsYData4
public import CollatzPosDens.Seed.S05JointCertExistsYData5

/-!
# The joint table of the joint certificate and its checker

This file defines the explicit joint table `𝖸 = (𝖸_q)_{1 ≤ q ≤ 8}` over the offset-law table
`g = CollatzPosDens.jointCertG`, and a Boolean checker whose value `true` at an entry implies the
condition of `CollatzPosDens.IsJointCert` there.

At each level `1 ≤ q ≤ 8` the pairs `(r, k) ∈ G_q × {0, …, 6198}` with `𝖸_q(r, k) ≠ 0` are listed
as positions `0 ≤ p < ℓ_q` of a table, in increasing order of the *key* `r̃ 2^13 + k`; position
`p` holds the key `κ_q(p)` and the value `v_q(p)`. The table `𝖸_q(r, k)` is `v_q(p)` at the
position `p` with `κ_q(p) = r̃ 2^13 + k`, and `0` if there is none. Since the keys increase, a
position is determined by its key, and `𝖸_q(r, k) = v_q(p)` whenever `κ_q(p) = r̃ 2^13 + k`.

The checker bounds an entry `v_q(p)` by a sum of *verified terms*, read from a *witness*: a list
of numbers `10^4 a + p'` with increasing letters `1 ≤ a ≤ 60`. With `r̃ = ⌊κ_q(p) / 2^13⌋`,
`k = κ_q(p) mod 2^13` and `P = 2^a n_k - 512`, the term of `(a, p')` is `0` unless
`3 ∣ 2^a r̃ - 1`, and then

* at the level `q = 1`, it is `⌊2^{-a} ⌊2^62 𝖦₀(P / 1536)⌋⌋` if `p' = 9999` and
  `P / 1536 > ξ_6198`, and `⌊2^{-a} g_{p'}⌋` if `p'` is a verified index of `P`;
* at a level `q ≥ 2`, it is `⌊2^{-a} v_{q-1}(p')⌋` if `p' < ℓ_{q-1}`, the grid part
  `j = κ_{q-1}(p') mod 2^13` is a verified index of `P`, and the residue part
  `⌊κ_{q-1}(p') / 2^13⌋` is the representative of `dn_a(r)`;

and `0` otherwise. A verified term equals the joint contribution `c^{jt}_{g,𝖸}(q, r, k, a)`, so
the sum of the terms of a witness is at most `∑_{a=1}^{60} c^{jt}_{g,𝖸}(q, r, k, a)`.

## Main definitions

* `CollatzPosDens.jointCertYKey q p`, `CollatzPosDens.jointCertYVal q p`,
  `CollatzPosDens.jointCertYLen q`: the key `κ_q(p)`, the value `v_q(p)` and the length `ℓ_q`.
* `CollatzPosDens.jointCertY`: the joint table `𝖸`.
* `CollatzPosDens.jointCertYTerm q r̃ k a p'`: the verified term of `(a, p')`.
* `CollatzPosDens.jointCertYCheckAt q p ws`: the check of the entry `p` of level `q` against
  the witness `ws`.

## Main results

* `CollatzPosDens.jointCertY_key`: `𝖸_q(r, k) = v_q(p)` when `κ_q(p) = r̃ 2^13 + k`.
* `CollatzPosDens.jointCertYTerm_le`: a term is at most the joint contribution.
* `CollatzPosDens.isJointCert_jointCertY_of_levelOK`: if every entry passes the check against
  some witness, then `𝖸` is a joint certificate over `g`.
* `CollatzPosDens.jointCertY_top`: `𝖸_8([6275]_8, 384) = 617014680840434`.

## Implementation notes

The keys and values of each level are kept in blocks of `256`, each block packed as one natural
number with `32`-bit (keys) and `64`-bit (values) lanes. The witnesses are not part of the table:
they are supplied to the kernel evaluations of the checker.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-! ### The tables -/

/-- The keys of level `1`, in blocks of `256`. -/
def jointCertYKeys1 : List ℕ :=
  [jointCertYKeyBlock1_0, jointCertYKeyBlock1_1, jointCertYKeyBlock1_2, jointCertYKeyBlock1_3,
    jointCertYKeyBlock1_4, jointCertYKeyBlock1_5, jointCertYKeyBlock1_6, jointCertYKeyBlock1_7,
    jointCertYKeyBlock1_8, jointCertYKeyBlock1_9, jointCertYKeyBlock1_10,
    jointCertYKeyBlock1_11]

/-- The values of level `1`, in blocks of `256`. -/
def jointCertYVals1 : List ℕ :=
  [jointCertYValBlock1_0, jointCertYValBlock1_1, jointCertYValBlock1_2, jointCertYValBlock1_3,
    jointCertYValBlock1_4, jointCertYValBlock1_5, jointCertYValBlock1_6, jointCertYValBlock1_7,
    jointCertYValBlock1_8, jointCertYValBlock1_9, jointCertYValBlock1_10,
    jointCertYValBlock1_11]

/-- The keys of level `2`, in blocks of `256`. -/
def jointCertYKeys2 : List ℕ :=
  [jointCertYKeyBlock2_0, jointCertYKeyBlock2_1, jointCertYKeyBlock2_2, jointCertYKeyBlock2_3,
    jointCertYKeyBlock2_4, jointCertYKeyBlock2_5, jointCertYKeyBlock2_6, jointCertYKeyBlock2_7,
    jointCertYKeyBlock2_8, jointCertYKeyBlock2_9, jointCertYKeyBlock2_10,
    jointCertYKeyBlock2_11, jointCertYKeyBlock2_12, jointCertYKeyBlock2_13,
    jointCertYKeyBlock2_14, jointCertYKeyBlock2_15, jointCertYKeyBlock2_16,
    jointCertYKeyBlock2_17, jointCertYKeyBlock2_18, jointCertYKeyBlock2_19,
    jointCertYKeyBlock2_20, jointCertYKeyBlock2_21]

/-- The values of level `2`, in blocks of `256`. -/
def jointCertYVals2 : List ℕ :=
  [jointCertYValBlock2_0, jointCertYValBlock2_1, jointCertYValBlock2_2, jointCertYValBlock2_3,
    jointCertYValBlock2_4, jointCertYValBlock2_5, jointCertYValBlock2_6, jointCertYValBlock2_7,
    jointCertYValBlock2_8, jointCertYValBlock2_9, jointCertYValBlock2_10,
    jointCertYValBlock2_11, jointCertYValBlock2_12, jointCertYValBlock2_13,
    jointCertYValBlock2_14, jointCertYValBlock2_15, jointCertYValBlock2_16,
    jointCertYValBlock2_17, jointCertYValBlock2_18, jointCertYValBlock2_19,
    jointCertYValBlock2_20, jointCertYValBlock2_21]

/-- The keys of level `3`, in blocks of `256`. -/
def jointCertYKeys3 : List ℕ :=
  [jointCertYKeyBlock3_0, jointCertYKeyBlock3_1, jointCertYKeyBlock3_2, jointCertYKeyBlock3_3,
    jointCertYKeyBlock3_4, jointCertYKeyBlock3_5, jointCertYKeyBlock3_6, jointCertYKeyBlock3_7,
    jointCertYKeyBlock3_8, jointCertYKeyBlock3_9, jointCertYKeyBlock3_10,
    jointCertYKeyBlock3_11, jointCertYKeyBlock3_12, jointCertYKeyBlock3_13,
    jointCertYKeyBlock3_14, jointCertYKeyBlock3_15, jointCertYKeyBlock3_16,
    jointCertYKeyBlock3_17, jointCertYKeyBlock3_18, jointCertYKeyBlock3_19,
    jointCertYKeyBlock3_20, jointCertYKeyBlock3_21, jointCertYKeyBlock3_22,
    jointCertYKeyBlock3_23]

/-- The values of level `3`, in blocks of `256`. -/
def jointCertYVals3 : List ℕ :=
  [jointCertYValBlock3_0, jointCertYValBlock3_1, jointCertYValBlock3_2, jointCertYValBlock3_3,
    jointCertYValBlock3_4, jointCertYValBlock3_5, jointCertYValBlock3_6, jointCertYValBlock3_7,
    jointCertYValBlock3_8, jointCertYValBlock3_9, jointCertYValBlock3_10,
    jointCertYValBlock3_11, jointCertYValBlock3_12, jointCertYValBlock3_13,
    jointCertYValBlock3_14, jointCertYValBlock3_15, jointCertYValBlock3_16,
    jointCertYValBlock3_17, jointCertYValBlock3_18, jointCertYValBlock3_19,
    jointCertYValBlock3_20, jointCertYValBlock3_21, jointCertYValBlock3_22,
    jointCertYValBlock3_23]

/-- The keys of level `4`, in blocks of `256`. -/
def jointCertYKeys4 : List ℕ :=
  [jointCertYKeyBlock4_0, jointCertYKeyBlock4_1, jointCertYKeyBlock4_2, jointCertYKeyBlock4_3,
    jointCertYKeyBlock4_4, jointCertYKeyBlock4_5, jointCertYKeyBlock4_6, jointCertYKeyBlock4_7,
    jointCertYKeyBlock4_8, jointCertYKeyBlock4_9, jointCertYKeyBlock4_10,
    jointCertYKeyBlock4_11, jointCertYKeyBlock4_12, jointCertYKeyBlock4_13]

/-- The values of level `4`, in blocks of `256`. -/
def jointCertYVals4 : List ℕ :=
  [jointCertYValBlock4_0, jointCertYValBlock4_1, jointCertYValBlock4_2, jointCertYValBlock4_3,
    jointCertYValBlock4_4, jointCertYValBlock4_5, jointCertYValBlock4_6, jointCertYValBlock4_7,
    jointCertYValBlock4_8, jointCertYValBlock4_9, jointCertYValBlock4_10,
    jointCertYValBlock4_11, jointCertYValBlock4_12, jointCertYValBlock4_13]

/-- The keys of level `5`, in blocks of `256`. -/
def jointCertYKeys5 : List ℕ :=
  [jointCertYKeyBlock5_0, jointCertYKeyBlock5_1, jointCertYKeyBlock5_2, jointCertYKeyBlock5_3]

/-- The values of level `5`, in blocks of `256`. -/
def jointCertYVals5 : List ℕ :=
  [jointCertYValBlock5_0, jointCertYValBlock5_1, jointCertYValBlock5_2, jointCertYValBlock5_3]

/-- The keys of level `6`, in blocks of `256`. -/
def jointCertYKeys6 : List ℕ :=
  [jointCertYKeyBlock6_0]

/-- The values of level `6`, in blocks of `256`. -/
def jointCertYVals6 : List ℕ :=
  [jointCertYValBlock6_0]

/-- The keys of level `7`, in blocks of `256`. -/
def jointCertYKeys7 : List ℕ :=
  [jointCertYKeyBlock7_0]

/-- The values of level `7`, in blocks of `256`. -/
def jointCertYVals7 : List ℕ :=
  [jointCertYValBlock7_0]

/-- The keys of level `8`, in blocks of `256`. -/
def jointCertYKeys8 : List ℕ :=
  [jointCertYKeyBlock8_0]

/-- The values of level `8`, in blocks of `256`. -/
def jointCertYVals8 : List ℕ :=
  [jointCertYValBlock8_0]

/-- The key blocks of the level `q`. -/
def jointCertYKeyList : ℕ → List ℕ
  | 1 => jointCertYKeys1
  | 2 => jointCertYKeys2
  | 3 => jointCertYKeys3
  | 4 => jointCertYKeys4
  | 5 => jointCertYKeys5
  | 6 => jointCertYKeys6
  | 7 => jointCertYKeys7
  | 8 => jointCertYKeys8
  | _ => []

/-- The value blocks of the level `q`. -/
def jointCertYValList : ℕ → List ℕ
  | 1 => jointCertYVals1
  | 2 => jointCertYVals2
  | 3 => jointCertYVals3
  | 4 => jointCertYVals4
  | 5 => jointCertYVals5
  | 6 => jointCertYVals6
  | 7 => jointCertYVals7
  | 8 => jointCertYVals8
  | _ => []

/-- The number `ℓ_q` of listed entries of the level `q` (`0` outside `1 ≤ q ≤ 8`). -/
def jointCertYLen : ℕ → ℕ
  | 1 => 3043
  | 2 => 5504
  | 3 => 6076
  | 4 => 3502
  | 5 => 907
  | 6 => 145
  | 7 => 16
  | 8 => 1
  | _ => 0

/-- The key `κ_q(p) = r̃ 2^13 + k` at the position `p` of the level `q`. -/
def jointCertYKey (q p : ℕ) : ℕ :=
  jointCertBlockLane 32 (jointCertYKeyList q) p

/-- The value `v_q(p)` at the position `p` of the level `q`. -/
def jointCertYVal (q p : ℕ) : ℕ :=
  jointCertBlockLane 64 (jointCertYValList q) p

/-- The value of the level `q` at the key `x`: `v_q(p)` for the least position `p < ℓ_q` with
`κ_q(p) = x`, and `0` if there is none. -/
def jointCertYLookup (q x : ℕ) : ℕ :=
  if h : ∃ p, p < jointCertYLen q ∧ jointCertYKey q p = x then jointCertYVal q (Nat.find h)
  else 0

/-- The joint table `𝖸_q(r, k)`: the value of the level `q` at the key `r̃ 2^13 + k`. -/
def jointCertY (q : ℕ) (r : ResidueGroup q) (k : Fin 6199) : ℕ :=
  jointCertYLookup q (r.val * 8192 + k)

/-! ### Increasing keys -/

/-- The check `κ_q(p) < κ_q(p + 1)` for `lo ≤ p < lo + n`. -/
def jointCertYSortedFrom (q : ℕ) (n : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih p => Nat.blt (jointCertYKey q p) (jointCertYKey q (p + 1)) && ih (p + 1)) n

/-- The keys of the level `q` increase: `κ_q(p) < κ_q(p + 1)` for `p + 1 < ℓ_q`. -/
def jointCertYSorted (q : ℕ) : Bool :=
  jointCertYSortedFrom q (jointCertYLen q - 1) 0

/-- A passed check of increasing keys from `lo` gives `κ_q(p) < κ_q(p + 1)` on its range. -/
theorem jointCertYKey_lt_succ_of_sortedFrom {q : ℕ} :
    ∀ {n lo : ℕ}, jointCertYSortedFrom q n lo = true → ∀ p, lo ≤ p → p < lo + n →
      jointCertYKey q p < jointCertYKey q (p + 1)
  | 0, _, _, p, _, h2 => absurd h2 (by omega)
  | n + 1, lo, h, p, h1, h2 => by
    change (Nat.blt (jointCertYKey q lo) (jointCertYKey q (lo + 1)) &&
      jointCertYSortedFrom q n (lo + 1)) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    rcases h1.eq_or_lt with rfl | h1
    · exact h.1
    · exact jointCertYKey_lt_succ_of_sortedFrom h.2 p h1 (by omega)

/-- With increasing keys, `κ_q` is strictly increasing on the positions `p < ℓ_q`. -/
theorem jointCertYKey_lt_of_sorted {q : ℕ} (hs : jointCertYSorted q = true) {p₁ p₂ : ℕ}
    (h : p₁ < p₂) (h₂ : p₂ < jointCertYLen q) : jointCertYKey q p₁ < jointCertYKey q p₂ := by
  induction p₂ with
  | zero => omega
  | succ p ih =>
    have hstep := jointCertYKey_lt_succ_of_sortedFrom hs p (Nat.zero_le p) (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact (ih h (by omega)).trans hstep
    · exact hstep

/-- With increasing keys, the value of the level `q` at the key `κ_q(p)` is `v_q(p)`. -/
theorem jointCertYLookup_key {q p : ℕ} (hs : jointCertYSorted q = true)
    (hp : p < jointCertYLen q) : jointCertYLookup q (jointCertYKey q p) = jointCertYVal q p := by
  have h : ∃ p', p' < jointCertYLen q ∧ jointCertYKey q p' = jointCertYKey q p := ⟨p, hp, rfl⟩
  rw [jointCertYLookup, dite_eq_left_of_eq_true (eq_true h)]
  congr 1
  have hspec := Nat.find_spec h
  rcases lt_trichotomy (Nat.find h) p with hlt | heq | hgt
  · exact absurd hspec.2 (jointCertYKey_lt_of_sorted hs hlt hp).ne
  · exact heq
  · exact absurd hspec.2 (jointCertYKey_lt_of_sorted hs hgt hspec.1).ne'

/-- A nonzero value at a key `x` is the value `v_q(p)` at a position `p < ℓ_q` with
`κ_q(p) = x`. -/
theorem exists_of_jointCertYLookup_ne_zero {q x : ℕ} (h : jointCertYLookup q x ≠ 0) :
    ∃ p, p < jointCertYLen q ∧ jointCertYKey q p = x ∧
      jointCertYLookup q x = jointCertYVal q p := by
  rw [jointCertYLookup] at h ⊢
  split_ifs at h ⊢ with hx
  · exact ⟨Nat.find hx, (Nat.find_spec hx).1, (Nat.find_spec hx).2, rfl⟩
  · exact absurd rfl h

/-- `𝖸_q(r, k) = v_q(p)` whenever `κ_q(p) = r̃ 2^13 + k`, for increasing keys. -/
theorem jointCertY_key {q p : ℕ} (hs : jointCertYSorted q = true) (hp : p < jointCertYLen q)
    (r : ResidueGroup q) (k : Fin 6199) (h : jointCertYKey q p = r.val * 8192 + k) :
    jointCertY q r k = jointCertYVal q p := by
  rw [jointCertY, ← h, jointCertYLookup_key hs hp]

/-- The keys of every level `q ≤ 8` increase. -/
theorem jointCertYSorted_of_le {q : ℕ} (hq : q ≤ 8) : jointCertYSorted q = true := by
  have h : ∀ q < 9, jointCertYSorted q = true := by decide +kernel
  exact h q (by omega)

/-! ### Verified terms -/

/-- The verified term of the pair `(a, p')` for an entry with residue representative `rr` and
grid index `kk` of the level `q`; see the module docstring. -/
def jointCertYTerm (q rr kk a p' : ℕ) : ℕ :=
  cond (Nat.beq (2 ^ a * rr % 3) 1)
    (cond (Nat.beq q 1)
      (cond (Nat.beq p' 9999)
        (cond (Nat.ble 512 (2 ^ a * jointCertGridTab kk) &&
            Nat.blt (3 * 583351470707564294) (2 ^ a * jointCertGridTab kk - 512))
          (offlawFloorNum 62 (2 ^ a * jointCertGridTab kk - 512) 1536 / 2 ^ a) 0)
        (cond (Nat.ble 512 (2 ^ a * jointCertGridTab kk) &&
            jointCertIndexOK (2 ^ a * jointCertGridTab kk - 512) p')
          (jointCertGTab p' / 2 ^ a) 0))
      (cond (Nat.blt p' (jointCertYLen (q - 1)) && Nat.ble 512 (2 ^ a * jointCertGridTab kk) &&
          jointCertIndexOK (2 ^ a * jointCertGridTab kk - 512) (jointCertYKey (q - 1) p' % 8192) &&
          Nat.beq (jointCertYKey (q - 1) p' / 8192) ((2 ^ a * rr - 1) / 3 % 3 ^ (q - 1)))
        (jointCertYVal (q - 1) p' / 2 ^ a) 0))
    0

/-- A verified term is at most the joint contribution:
`jointCertYTerm q r̃ k a p' ≤ c^{jt}_{g,𝖸}(q, r, k, a)`, for increasing keys at the level
`q - 1`. -/
theorem jointCertYTerm_le {q : ℕ} (hs : jointCertYSorted (q - 1) = true) (r : ResidueGroup q)
    (k : Fin 6199) (a p' : ℕ) :
    jointCertYTerm q r.val k a p' ≤ jointContrib jointCertG jointCertY q r k a := by
  rw [jointCertYTerm, jointCertGridTab_eq (by omega)]
  cases hres : Nat.beq (2 ^ a * r.val % 3) 1
  · exact Nat.zero_le _
  rw [Nat.beq_eq] at hres
  rw [Bool.cond_true]
  by_cases hq : q = 1
  · subst hq
    have hc : jointContrib jointCertG jointCertY 1 r k a = offlawContrib jointCertG k a := by
      simp [jointContrib, hres]
    rw [hc, show Nat.beq 1 1 = true from rfl, Bool.cond_true]
    by_cases hp : p' = 9999
    · rw [show Nat.beq p' 9999 = true from Nat.beq_eq ▸ hp, Bool.cond_true]
      cases h1 : (Nat.ble 512 (2 ^ a * offlawGridNum k) &&
          Nat.blt (3 * 583351470707564294) (2 ^ a * offlawGridNum k - 512))
      · exact Nat.zero_le _
      · rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h1
        simp [offlawContrib, Nat.not_lt.2 h1.1, h1.2]
    · rw [show Nat.beq p' 9999 = false from by
        rw [← Bool.not_eq_true, Nat.beq_eq]; exact hp, Bool.cond_false]
      cases h1 : (Nat.ble 512 (2 ^ a * offlawGridNum k) &&
          jointCertIndexOK (2 ^ a * offlawGridNum k - 512) p')
      · exact Nat.zero_le _
      · rw [Bool.and_eq_true, Nat.ble_eq] at h1
        obtain ⟨hj, hj1, hj2, hj3⟩ := jointCertIndexOK_spec h1.2
        exact (offlawContrib_of_index jointCertG ⟨p', hj⟩ h1.1 hj1 hj2 hj3).symm.le
  · rw [show Nat.beq q 1 = false from by rw [← Bool.not_eq_true, Nat.beq_eq]; exact hq,
      Bool.cond_false]
    cases h1 : (Nat.blt p' (jointCertYLen (q - 1)) && Nat.ble 512 (2 ^ a * offlawGridNum k) &&
        jointCertIndexOK (2 ^ a * offlawGridNum k - 512) (jointCertYKey (q - 1) p' % 8192) &&
        Nat.beq (jointCertYKey (q - 1) p' / 8192) ((2 ^ a * r.val - 1) / 3 % 3 ^ (q - 1)))
    · exact Nat.zero_le _
    · simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at h1
      obtain ⟨⟨⟨hp, hle⟩, hidx⟩, hres'⟩ := h1
      obtain ⟨hj, hj1, hj2, hj3⟩ := jointCertIndexOK_spec hidx
      rw [jointContrib_of_index jointCertG jointCertY r ⟨_, hj⟩ hres hq hle hj1 hj2 hj3]
      refine (Nat.div_le_div_right (le_of_eq ?_))
      have hval : (childResidue a r).val = (2 ^ a * r.val - 1) / 3 % 3 ^ (q - 1) := by
        rw [childResidue_def, ZMod.val_natCast]
      refine (jointCertY_key hs hp _ _ ?_).symm
      rw [hval, ← hres', Fin.val_mk, Nat.div_add_mod']

/-! ### The checker -/

/-- The sum of the verified terms of a witness `ws` (a list of numbers `10^4 a + p'`) for an
entry with residue representative `rr` and grid index `kk` of the level `q`, the letters being
required to increase from `lo` up to `60` (the sum stops at the first violation). -/
def jointCertYWitSum (q rr kk : ℕ) (ws : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun l _ ih lo => cond (Nat.ble lo (l / 10000) && Nat.ble (l / 10000) 60)
      (Nat.add (jointCertYTerm q rr kk (l / 10000) (l % 10000)) (ih (l / 10000 + 1))) 0) ws

/-- The sum of the verified terms of a witness is at most
`∑_{a=lo}^{60} c^{jt}_{g,𝖸}(q, r, k, a)`. -/
theorem jointCertYWitSum_le {q : ℕ} (hs : jointCertYSorted (q - 1) = true)
    (r : ResidueGroup q) (k : Fin 6199) :
    ∀ (ws : List ℕ) (lo : ℕ), jointCertYWitSum q r.val k ws lo ≤
      ∑ a ∈ Icc lo 60, jointContrib jointCertG jointCertY q r k a
  | [], _ => Nat.zero_le _
  | l :: ws, lo => by
    change cond (Nat.ble lo (l / 10000) && Nat.ble (l / 10000) 60)
      (Nat.add (jointCertYTerm q r.val k (l / 10000) (l % 10000))
        (jointCertYWitSum q r.val k ws (l / 10000 + 1))) 0 ≤ _
    cases h : (Nat.ble lo (l / 10000) && Nat.ble (l / 10000) 60)
    · exact Nat.zero_le _
    · rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
      rw [Bool.cond_true]
      have hnot : l / 10000 ∉ Icc (l / 10000 + 1) 60 := by simp
      have hsub : insert (l / 10000) (Icc (l / 10000 + 1) 60) ⊆ Icc lo 60 := by
        intro x hx
        simp only [mem_insert, mem_Icc] at hx ⊢
        omega
      refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
      rw [Finset.sum_insert hnot]
      exact Nat.add_le_add (jointCertYTerm_le hs r k _ _) (jointCertYWitSum_le hs r k ws _)

/-- The check of the entry `p` of the level `q` against the witness `ws`:
`v_q(p)` is at most the sum of the verified terms of `ws`. -/
def jointCertYCheckAt (q p : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble (jointCertYVal q p)
    (jointCertYWitSum q (jointCertYKey q p / 8192) (jointCertYKey q p % 8192) ws 1)

/-- The check of the entries `p, p + 1, …` of the level `q` against the witnesses `wss`, in
order. -/
def jointCertYCheckList (q : ℕ) (wss : List (List ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun ws _ ih p => jointCertYCheckAt q p ws && ih (p + 1)) wss

/-- Every entry `lo ≤ p < hi` of the level `q` passes the check against some witness. -/
def JointCertYLevelOK (q lo hi : ℕ) : Prop :=
  ∀ p, lo ≤ p → p < hi → ∃ ws, jointCertYCheckAt q p ws = true

/-- A passed list check covers the entries `lo ≤ p < lo + n`, `n` the number of witnesses. -/
theorem jointCertYLevelOK_of_checkList {q : ℕ} :
    ∀ {wss : List (List ℕ)} {lo n : ℕ}, jointCertYCheckList q wss lo = true →
      wss.length = n → JointCertYLevelOK q lo (lo + n)
  | [], _, _, _, hn, p, h1, h2 => absurd h2 (by simp at hn; omega)
  | ws :: wss, lo, n, h, hn, p, h1, h2 => by
    change (jointCertYCheckAt q lo ws && jointCertYCheckList q wss (lo + 1)) = true at h
    rw [Bool.and_eq_true] at h
    rcases h1.eq_or_lt with rfl | h1
    · exact ⟨ws, h.1⟩
    · simp only [List.length_cons] at hn
      exact jointCertYLevelOK_of_checkList h.2 rfl p h1 (by omega)

/-- Checked ranges of entries concatenate. -/
theorem JointCertYLevelOK.trans {q a b c : ℕ} (h₁ : JointCertYLevelOK q a b)
    (h₂ : JointCertYLevelOK q b c) : JointCertYLevelOK q a c := fun p ha hc => by
  rcases Nat.lt_or_ge p b with hb | hb
  · exact h₁ p ha hb
  · exact h₂ p hb hc

/-- If every listed entry of every level `1 ≤ q ≤ 8` passes the check against some witness,
then `𝖸` is a joint certificate over `g`. -/
theorem isJointCert_jointCertY_of_levelOK
    (hok : ∀ q, 1 ≤ q → q ≤ 8 → JointCertYLevelOK q 0 (jointCertYLen q)) :
    IsJointCert jointCertG jointCertY := by
  rw [isJointCert_iff_of_ne_zero]
  intro q h1 h8 k r hne
  obtain ⟨p, hp, hkey, hval⟩ := exists_of_jointCertYLookup_ne_zero hne
  obtain ⟨ws, hws⟩ := hok q h1 h8 p (Nat.zero_le p) hp
  rw [jointCertYCheckAt, Nat.ble_eq, hkey] at hws
  have hr : (r.val * 8192 + k) / 8192 = r.val := by omega
  have hk : (r.val * 8192 + k) % 8192 = k := by omega
  rw [hr, hk] at hws
  change jointCertYLookup q (r.val * 8192 + k) ≤ _
  rw [hval]
  exact hws.trans (jointCertYWitSum_le (jointCertYSorted_of_le (by omega)) r k ws 1)

/-- The top value: `𝖸_8([6275]_8, 384) = 617014680840434`. -/
theorem jointCertY_top : jointCertY 8 (6275 : ResidueGroup 8) 384 = 617014680840434 := by
  have hkey : jointCertYKey 8 0 = (6275 : ResidueGroup 8).val * 8192 + ((384 : Fin 6199) : ℕ) := by
    decide +kernel
  rw [jointCertY_key (jointCertYSorted_of_le le_rfl) (by decide) _ _ hkey]
  decide +kernel

end CollatzPosDens
