/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05ChildResidue
public import CollatzPosDens.Transfer.ResidueMap
public import CollatzPosDens.Transfer.S02Reduction

/-!
# The prefix residue of a word

For `q ∈ ℕ` and a word `u` with `|u| ≥ q`, the *prefix residue* `pr_q(u) = [off(u_{≤ q})]_q ∈ G_q`
is the residue modulo `3^q` of the offset of the prefix of length `q` of `u`; here `[·]_q` is the
reduction `ℤ[1/2] → G_q` of dyadic rationals, which applies since offsets are dyadic.

Splitting off the first letter, `u = (a) v`, the offset satisfies
`off(u_{≤ q}) = 2^{-a} (1 + 3 off(v_{≤ q-1}))` for `q ≥ 1`, and this translates into a
one-step description of the prefix residue: `pr_q((a) v) = r` holds exactly when
`3 ∣ 2^a r̃ - 1` and `pr_{q-1}(v) = dn_a(r)`, where `dn_a(r)` is the child residue.

## Main definitions

* `CollatzPosDens.prefixResidue q u`: the prefix residue `pr_q(u) ∈ G_q`.

## Main results

* `CollatzPosDens.residueReduction_prefixResidue`: reducing `pr_q(u)` modulo `3^m`, `m ≤ q`, gives
  the residue modulo `3^m` of `off(u_{≤ q})`.
* `CollatzPosDens.prefixResidue_cons_eq_iff`: for `q ≥ 1`, `pr_q((a) v) = r` if and only if
  `3 ∣ 2^a r̃ - 1` and `pr_{q-1}(v) = dn_a(r)`.

## Implementation notes

The prefix residue is defined for every word, with `u_{≤ q} = List.take q u`; when `|u| < q`
this prefix is `u` itself. For words with `|u| ≥ q` this is the prefix of length `q`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The **prefix residue** `pr_q(u) = [off(u_{≤ q})]_q ∈ G_q`: the residue modulo `3^q` of the
offset of the prefix `u_{≤ q}` (`List.take q u`) of the word `u`. -/
@[collatz_pos_dens "def_s05_prefix_residue"]
noncomputable def prefixResidue (q : ℕ) (u : Word) : ResidueGroup q :=
  dyadicRed q ⟨off (u.take q), off_mem_dyadicRationals _⟩

/-- Unfolding lemma for `prefixResidue`. -/
theorem prefixResidue_def (q : ℕ) (u : Word) :
    prefixResidue q u = dyadicRed q ⟨off (u.take q), off_mem_dyadicRationals _⟩ :=
  rfl

/-- The prefix residue only depends on the prefix of length `q`. -/
theorem prefixResidue_take (q : ℕ) (u : Word) : prefixResidue q (u.take q) = prefixResidue q u := by
  simp only [prefixResidue_def, List.take_take, min_self]

/-- Reducing the residue `[x]_q` of a dyadic rational modulo `3^m`, `m ≤ q`, gives `[x]_m`. -/
private theorem residueReduction_dyadicRed_prefix {m q : ℕ} (h : m ≤ q) (x : dyadicRationals) :
    residueReduction h (dyadicRed q x) = dyadicRed m x :=
  RingHom.congr_fun (eq_dyadicRed ((residueReduction h).comp (dyadicRed q))) x

/-- Reducing `pr_q(u)` modulo `3^m`, for `m ≤ q`, gives `[off(u_{≤ q})]_m`. -/
theorem residueReduction_prefixResidue {m q : ℕ} (h : m ≤ q) (u : Word) :
    residueReduction h (prefixResidue q u) =
      dyadicRed m ⟨off (u.take q), off_mem_dyadicRationals _⟩ :=
  residueReduction_dyadicRed_prefix h _

/-- The residue of the offset of `(a) w` is `[off((a) w)]_q = 2^{-a} (1 + 3 [off(w)]_q)`. -/
theorem dyadicRed_off_cons (q : ℕ) (a : ℕ+) (w : Word) :
    dyadicRed q ⟨off (a :: w), off_mem_dyadicRationals _⟩ =
      2⁻¹ ^ (a : ℕ) * (1 + 3 * dyadicRed q ⟨off w, off_mem_dyadicRationals w⟩) := by
  have h := dyadicRed_off_append q [a] w
  rw [List.singleton_append] at h
  rw [h, dyadicRed_weight]
  have h1 : (⟨off [a], off_mem_dyadicRationals [a]⟩ : dyadicRationals) =
      ⟨((1 : ℤ) : ℚ) / 2 ^ (a : ℕ), intCast_div_two_pow_mem 1 a⟩ :=
    Subtype.ext (by simp)
  rw [h1, dyadicRed_div_two_pow, Word.valSum_singleton]
  simp only [Int.cast_one, one_mul, List.length_singleton, pow_one]
  ring

/-- The integer core of the one-step description of the prefix residue:
`3^{k+1} ∣ N - (1 + 3 o)` if and only if `3 ∣ N - 1` and `3^k ∣ (N - 1)/3 - o`. -/
theorem three_pow_succ_dvd_sub_iff (k : ℕ) (N o : ℤ) :
    (3 : ℤ) ^ (k + 1) ∣ N - (1 + 3 * o) ↔ 3 ∣ N - 1 ∧ (3 : ℤ) ^ k ∣ (N - 1) / 3 - o := by
  constructor
  · intro h
    have h3 : (3 : ℤ) ∣ N - 1 := by
      have := (dvd_pow_self (3 : ℤ) (Nat.succ_ne_zero k)).trans h
      have h' : N - 1 = (N - (1 + 3 * o)) + 3 * o := by ring
      rw [h']
      exact dvd_add this (dvd_mul_right 3 o)
    obtain ⟨m, hm⟩ := h3
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [hm, Int.mul_ediv_cancel_left _ (by norm_num)]
    have h' : N - (1 + 3 * o) = 3 * (m - o) := by linear_combination hm
    rw [h', pow_succ', mul_dvd_mul_iff_left (by norm_num)] at h
    exact h
  · rintro ⟨⟨m, hm⟩, h⟩
    rw [hm, Int.mul_ediv_cancel_left _ (by norm_num)] at h
    have h' : N - (1 + 3 * o) = 3 * (m - o) := by linear_combination hm
    rw [h', pow_succ']
    exact mul_dvd_mul_left 3 h

/-- **One-step description of the prefix residue**: for `q ≥ 1`, a letter `a` and a word `v`,
`pr_q((a) v) = r` if and only if `3 ∣ 2^a r̃ - 1` and `pr_{q-1}(v) = dn_a(r)`. -/
theorem prefixResidue_cons_eq_iff {q : ℕ} (hq : 1 ≤ q) (a : ℕ+) (v : Word)
    (r : ResidueGroup q) :
    prefixResidue q (a :: v) = r ↔
      (3 : ℤ) ∣ 2 ^ (a : ℕ) * (r.val : ℤ) - 1 ∧ prefixResidue (q - 1) v = childResidue a r := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  change prefixResidue (k + 1) (a :: v) = r ↔
    (3 : ℤ) ∣ 2 ^ (a : ℕ) * (r.val : ℤ) - 1 ∧ prefixResidue k v = childResidue a r
  set o := dyadicRed (k + 1) ⟨off (v.take k), off_mem_dyadicRationals _⟩ with ho
  have hpr : prefixResidue (k + 1) (a :: v) = 2⁻¹ ^ (a : ℕ) * (1 + 3 * o) := by
    rw [prefixResidue_def, List.take_succ_cons, dyadicRed_off_cons]
  have hpk : prefixResidue k v = ((o.val : ℕ) : ResidueGroup k) := by
    have h := residueReduction_dyadicRed_prefix (Nat.le_succ k)
      ⟨off (v.take k), off_mem_dyadicRationals _⟩
    rw [prefixResidue_def, ← h, ← ho]
    conv_lhs => rw [← ZMod.natCast_zmod_val o]
    exact residueReduction_natCast _ _
  have hu : IsUnit ((2 : ResidueGroup (k + 1)) ^ (a : ℕ)) :=
    (isUnit_two_residueGroup _).pow _
  have hstep : prefixResidue (k + 1) (a :: v) = r ↔
      (((1 + 3 * (o.val : ℤ)) : ℤ) : ResidueGroup (k + 1)) =
        ((2 ^ (a : ℕ) * (r.val : ℤ) : ℤ) : ResidueGroup (k + 1)) := by
    rw [hpr, ← hu.mul_right_inj, ← mul_assoc, two_pow_mul_inv_two_pow, one_mul]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hstep, ZMod.intCast_eq_intCast_iff_dvd_sub, hpk]
  push_cast
  rw [three_pow_succ_dvd_sub_iff]
  refine and_congr_right fun h3 => ?_
  rw [childResidue_eq_intCast a r h3, ← Int.cast_natCast (R := ResidueGroup k),
    ZMod.intCast_eq_intCast_iff_dvd_sub]
  push_cast
  rfl

end CollatzPosDens
