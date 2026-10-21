/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# The child residue

Let `q ≥ 1`, let `r ∈ G_q = ℤ/3^qℤ` with least nonnegative representative `r̃`, and let `a ≥ 1`
be a letter with `3 ∣ 2^a r̃ - 1`. Then `(2^a r̃ - 1)/3` is an integer, and its residue modulo
`3^{q-1}` is the *child residue* `dn_a(r) ∈ G_{q-1}`. It is the residue reached from `r` by one
inverse Collatz step with valuation `a`.

## Main definitions

* `CollatzPosDens.childResidue a r`: the child residue `dn_a(r) ∈ G_{q-1}`, in natural-number
  arithmetic.

## Main results

* `CollatzPosDens.childResidue_eq_intCast`: when `3 ∣ 2^a r̃ - 1` in `ℤ`, the child residue is
  the residue of the integer `(2^a r̃ - 1)/3`.
* `CollatzPosDens.int_dvd_two_pow_mul_val_sub_one_iff`: `3 ∣ 2^a r̃ - 1` in `ℤ` exactly when
  `2^a r̃ ≡ 1 (mod 3)`, a decidable natural-number condition.
* `CollatzPosDens.childResidue_eq_of_modEq`: the child residue only depends on `2^a r̃` modulo
  `3^q`, so it is computed from any `m ≡ 2^a r̃ (mod 3^q)` with `m ≡ 1 (mod 3)`.

## Implementation notes

The definition is total: it is `(2^a r̃ - 1)/3` with truncated subtraction and division in `ℕ`,
cast to `G_{q-1}`. Under the hypothesis `3 ∣ 2^a r̃ - 1` in `ℤ` it is the residue of the integer
`(2^a r̃ - 1)/3` (`CollatzPosDens.childResidue_eq_intCast`); neither `q ≥ 1` nor `a ≥ 1` is
needed for that. The natural-number condition `2^a r̃ % 3 = 1` is the form of the hypothesis
used in computations, since `3 ∣ 0 - 1` holds in `ℕ` but `3 ∣ -1` fails in `ℤ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Child residue** `dn_a(r) ∈ G_{q-1}`: the residue modulo `3^{q-1}` of `(2^a r̃ - 1)/3`,
where `r̃ = r.val`. Computed in `ℕ`; under the hypothesis `3 ∣ 2^a r̃ - 1` (in `ℤ`) this is the
residue of the integer `(2^a r̃ - 1)/3`, see `childResidue_eq_intCast`. -/
@[collatz_pos_dens "def_s05_child_residue"]
def childResidue (a : ℕ) {q : ℕ} (r : ResidueGroup q) : ResidueGroup (q - 1) :=
  (((2 ^ a * r.val - 1) / 3 : ℕ) : ResidueGroup (q - 1))

/-- Unfolding lemma for the child residue. -/
theorem childResidue_def (a : ℕ) {q : ℕ} (r : ResidueGroup q) :
    childResidue a r = (((2 ^ a * r.val - 1) / 3 : ℕ) : ResidueGroup (q - 1)) :=
  rfl

/-- `3 ∣ 2^a r̃ - 1` in `ℤ` iff `2^a r̃ % 3 = 1` in `ℕ`. -/
theorem int_dvd_two_pow_mul_val_sub_one_iff (a : ℕ) {q : ℕ} (r : ResidueGroup q) :
    (3 : ℤ) ∣ 2 ^ a * (r.val : ℤ) - 1 ↔ 2 ^ a * r.val % 3 = 1 := by
  have h : (2 : ℤ) ^ a * (r.val : ℤ) = ((2 ^ a * r.val : ℕ) : ℤ) := by push_cast; rfl
  rw [h]
  generalize 2 ^ a * r.val = x
  omega

/-- **The child residue is the residue of `(2^a r̃ - 1)/3`**: if `3 ∣ 2^a r̃ - 1` in `ℤ`, then
`dn_a(r)` is the residue modulo `3^{q-1}` of the integer `(2^a r̃ - 1)/3`. -/
@[collatz_pos_dens "def_s05_child_residue"]
theorem childResidue_eq_intCast (a : ℕ) {q : ℕ} (r : ResidueGroup q)
    (h : (3 : ℤ) ∣ 2 ^ a * (r.val : ℤ) - 1) :
    childResidue a r = (((2 ^ a * (r.val : ℤ) - 1) / 3 : ℤ) : ResidueGroup (q - 1)) := by
  have hmod := (int_dvd_two_pow_mul_val_sub_one_iff a r).1 h
  have hle : 1 ≤ 2 ^ a * r.val := by omega
  have hcast : ((2 ^ a * r.val - 1 : ℕ) : ℤ) = 2 ^ a * (r.val : ℤ) - 1 := by
    rw [Nat.cast_sub hle]
    push_cast
    rfl
  rw [childResidue_def, ← Int.cast_natCast, Int.natCast_div, hcast]
  rfl

/-- The child residue only depends on `2^a r̃` modulo `3^q`: if `m ≡ 2^a r̃ (mod 3^q)` and
`m % 3 = 1`, then `dn_a(r)` is the residue of `(m - 1)/3`. -/
theorem childResidue_eq_of_modEq (a : ℕ) {q : ℕ} (r : ResidueGroup q) {m : ℕ}
    (hm : m ≡ 2 ^ a * r.val [MOD 3 ^ q]) (h1 : m % 3 = 1) :
    childResidue a r = (((m - 1) / 3 : ℕ) : ResidueGroup (q - 1)) := by
  rcases q with _ | q
  · exact @Subsingleton.elim (ZMod 1) _ _ _
  rw [childResidue_def, Nat.add_sub_cancel, ZMod.natCast_eq_natCast_iff]
  have h3 : m ≡ 2 ^ a * r.val [MOD 3] :=
    Nat.ModEq.of_dvd (Dvd.intro_left _ (pow_succ 3 q).symm) hm
  have hx : 2 ^ a * r.val % 3 = 1 := by unfold Nat.ModEq at h3; omega
  obtain ⟨u, hu⟩ : ∃ u, m = 3 * u + 1 := ⟨m / 3, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, 2 ^ a * r.val = 3 * v + 1 := ⟨2 ^ a * r.val / 3, by omega⟩
  rw [hu, hv, pow_succ, mul_comm (3 ^ q)] at hm
  rw [hu, hv, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.mul_div_cancel_left _ (by norm_num)]
  exact Nat.ModEq.mul_left_cancel' (by norm_num) (Nat.ModEq.add_right_cancel' 1 hm.symm)

end CollatzPosDens
