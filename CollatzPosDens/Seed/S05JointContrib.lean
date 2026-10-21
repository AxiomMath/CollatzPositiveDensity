/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05ChildResidue
public import CollatzPosDens.Seed.S05OfflawContrib

/-!
# Contributions of a joint table

Let `g = (g_0, …, g_6198)` be an offset-law table and let `𝖸 = (𝖸_q)_q` be a family of tables
`𝖸_q : G_q × {0, …, 6198} → ℕ`, where `G_q = ℤ/3^qℤ` is `CollatzPosDens.ResidueGroup q`, read
as step functions `2^{-62} 𝖸_q(r, ι(y))` on the offset grid `(ξ_k)`, with `ι` the grid index
`CollatzPosDens.offlawIndex`. For a level `q`, a residue `r ∈ G_q` with least nonnegative
representative `r̃`, a grid index `k` and a letter `a ≥ 1`, the one-letter recursion of the joint
offset law evaluates the level below at the child residue `dn_a(r)`
(`CollatzPosDens.childResidue`) and at the point
$$y_{k,a} = \frac{2^a \xi_k - 1}{3}.$$
The *joint contribution* `c^{jt}_{g,𝖸}(q, r, k, a) ∈ ℕ` is `0` if `3 ∤ 2^a r̃ - 1`; otherwise it
is the offset-law contribution `c_g(k,a)` (`CollatzPosDens.offlawContrib`) at level `q = 1`,
while for `q ≥ 2` it is `0` if `y_{k,a} < 0` or `y_{k,a} > ξ_6198`, and
$$\bigl\lfloor 2^{-a}\, 𝖸_{q-1}\bigl(\mathrm{dn}_a(r), \iota(y_{k,a})\bigr) \bigr\rfloor$$
if `0 ≤ y_{k,a} ≤ ξ_6198`.

As for `CollatzPosDens.offlawContrib`, writing `ξ_k = n_k / 512` with `n_k ∈ ℕ`, every case is
decided and every value computed in natural-number arithmetic: `y_{k,a} < 0` iff
`2^a n_k < 512`, and with `p = 2^a n_k - 512`, `y_{k,a} > ξ_6198` iff `3 n_6198 < p`; the
residue condition `3 ∣ 2^a r̃ - 1` is `2^a r̃ % 3 = 1`.

## Main definitions

* `CollatzPosDens.jointContrib g 𝖸 q r k a`: the joint contribution
  `c^{jt}_{g,𝖸}(q, r, k, a) ∈ ℕ`, in natural-number arithmetic.

## Main results

* `CollatzPosDens.jointContrib_of_not_dvd`, `CollatzPosDens.jointContrib_one`,
  `CollatzPosDens.jointContrib_of_neg`, `CollatzPosDens.jointContrib_of_lt`,
  `CollatzPosDens.jointContrib_of_nonneg_of_le`: the cases of the definition, stated with the
  integer divisibility `3 ∣ 2^a r̃ - 1`, the real point `y_{k,a}` and the grid index `ι`.
* `CollatzPosDens.jointContrib_of_index`: the contribution of an in-range point at a level
  `q ≥ 2`, given a verified grid index `j`, as `𝖸_{q-1}(dn_a(r), j) / 2^a`.

## Implementation notes

The family `𝖸` is a function of every level `q ∈ ℕ`; the contribution at a level `q ≥ 2` reads
only the level `q - 1`. The grid index ranges over `Fin 6199`. The contribution is defined for
all `q, k, a ∈ ℕ`; at the level `q = 0` it follows the clauses for `q ≥ 2`, and the case lemmas
for those clauses assume only `q ≠ 1`.

## References

* [Mazur, *Collatz positive density*], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Joint contribution** `c^{jt}_{g,𝖸}(q, r, k, a) ∈ ℕ`, with
`y_{k,a} = (2^a ξ_k - 1)/3 = (2^a n_k - 512)/1536`: it is `0` if `3 ∤ 2^a r̃ - 1`; otherwise
`c_g(k,a)` if `q = 1`; `0` if `q ≠ 1` and `y_{k,a} < 0` or `y_{k,a} > ξ_6198`; and
`⌊2^{-a} 𝖸_{q-1}(dn_a(r), ι(y_{k,a}))⌋` if `q ≠ 1` and `0 ≤ y_{k,a} ≤ ξ_6198`. Here
`583351470707564294 = n_6198` (`offlawGridNum_6198`). The case lemmas restate the clauses with
the integer divisibility and the real point `y_{k,a}`. -/
@[collatz_pos_dens "def_s05_joint_contrib"]
def jointContrib (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ) (q : ℕ)
    (r : ResidueGroup q) (k a : ℕ) : ℕ :=
  if 2 ^ a * r.val % 3 ≠ 1 then 0
  else if q = 1 then offlawContrib g k a
  else if 2 ^ a * offlawGridNum k < 512 then 0
  else if 3 * 583351470707564294 < 2 ^ a * offlawGridNum k - 512 then 0
  else Y (q - 1) (childResidue a r)
    ⟨offlawIndexNum (2 ^ a * offlawGridNum k - 512), offlawIndexNum_lt _⟩ / 2 ^ a

/-- The point `y_{k,a} = (2^a ξ_k - 1)/3` is `(2^a n_k - 512)/1536` in real form. -/
private theorem jointContrib_point (k a : ℕ) :
    ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 =
      ((2 ^ a * offlawGridNum k : ℕ) - 512 : ℝ) / 1536 := by
  rw [offlawGrid_eq_offlawGridNum]
  push_cast
  ring

/-- For `512 ≤ 2^a n_k`, `y_{k,a} = p / 1536` with `p = 2^a n_k - 512`. -/
private theorem jointContrib_point_of_le {k a : ℕ} (h : 512 ≤ 2 ^ a * offlawGridNum k) :
    ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 =
      ((2 ^ a * offlawGridNum k - 512 : ℕ) : ℝ) / 1536 := by
  rw [jointContrib_point, Nat.cast_sub h]
  norm_num

/-- `y_{k,a} < 0` iff `2^a n_k < 512`. -/
private theorem jointContrib_point_neg_iff (k a : ℕ) :
    ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 < 0 ↔ 2 ^ a * offlawGridNum k < 512 := by
  rw [jointContrib_point, div_neg_iff]
  have h : ((2 ^ a * offlawGridNum k : ℕ) : ℝ) < 512 ↔ 2 ^ a * offlawGridNum k < 512 := by
    exact_mod_cast Iff.rfl
  constructor
  · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · norm_num at h2
    · exact h.1 (by linarith)
  · intro h'
    exact Or.inr ⟨by linarith [h.2 h'], by norm_num⟩

/-- **Residue clause of `c^{jt}`**: if `3 ∤ 2^a r̃ - 1`, then `c^{jt}_{g,𝖸}(q, r, k, a) = 0`. -/
@[collatz_pos_dens "def_s05_joint_contrib"]
theorem jointContrib_of_not_dvd (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ)
    {q : ℕ} (r : ResidueGroup q) (k : ℕ) {a : ℕ} (h : ¬ (3 : ℤ) ∣ 2 ^ a * (r.val : ℤ) - 1) :
    jointContrib g Y q r k a = 0 := by
  rw [int_dvd_two_pow_mul_val_sub_one_iff] at h
  simp [jointContrib, h]

/-- **Level-one clause of `c^{jt}`**: if `3 ∣ 2^a r̃ - 1`, then
`c^{jt}_{g,𝖸}(1, r, k, a) = c_g(k,a)`. -/
@[collatz_pos_dens "def_s05_joint_contrib"]
theorem jointContrib_one (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ)
    (r : ResidueGroup 1) (k : ℕ) {a : ℕ} (h : (3 : ℤ) ∣ 2 ^ a * (r.val : ℤ) - 1) :
    jointContrib g Y 1 r k a = offlawContrib g k a := by
  rw [int_dvd_two_pow_mul_val_sub_one_iff] at h
  simp [jointContrib, h]

/-- **Negative clause of `c^{jt}`**: for `q ≠ 1`, if `y_{k,a} = (2^a ξ_k - 1)/3 < 0`, then
`c^{jt}_{g,𝖸}(q, r, k, a) = 0`. -/
@[collatz_pos_dens "def_s05_joint_contrib"]
theorem jointContrib_of_neg (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ)
    {q : ℕ} (r : ResidueGroup q) {k a : ℕ} (hq : q ≠ 1)
    (hy : ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 < 0) :
    jointContrib g Y q r k a = 0 := by
  rw [jointContrib_point_neg_iff] at hy
  simp [jointContrib, hq, hy]

/-- **Beyond-grid clause of `c^{jt}`**: for `q ≠ 1`, if `y_{k,a} = (2^a ξ_k - 1)/3 > ξ_6198`,
then `c^{jt}_{g,𝖸}(q, r, k, a) = 0`. -/
@[collatz_pos_dens "def_s05_joint_contrib"]
theorem jointContrib_of_lt (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ)
    {q : ℕ} (r : ResidueGroup q) {k a : ℕ} (hq : q ≠ 1)
    (hy : ((offlawGrid 6198 : ℚ) : ℝ) < ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3) :
    jointContrib g Y q r k a = 0 := by
  have h0 : (0 : ℝ) ≤ ((offlawGrid 6198 : ℚ) : ℝ) := by exact_mod_cast offlawGrid_nonneg 6198
  have hle : ¬ 2 ^ a * offlawGridNum k < 512 := by
    rw [← jointContrib_point_neg_iff]
    linarith
  rw [jointContrib_point_of_le (not_lt.1 hle)] at hy
  have hlt : 3 * 583351470707564294 < 2 ^ a * offlawGridNum k - 512 := by
    rw [← offlawGridNum_6198, ← not_le, ← natCast_div_le_offlawGrid_iff]
    exact not_le.2 hy
  simp [jointContrib, hq, hle, hlt]

/-- **In-range clause of `c^{jt}`**: for `q ≠ 1`, if `3 ∣ 2^a r̃ - 1` and
`0 ≤ y_{k,a} ≤ ξ_6198`, with `y_{k,a} = (2^a ξ_k - 1)/3`, then
`c^{jt}_{g,𝖸}(q, r, k, a) = ⌊2^{-a} 𝖸_{q-1}(dn_a(r), ι(y_{k,a}))⌋`. -/
@[collatz_pos_dens "def_s05_joint_contrib"]
theorem jointContrib_of_nonneg_of_le (g : Fin 6199 → ℕ)
    (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ) {q : ℕ} (r : ResidueGroup q) {k a : ℕ}
    (h : (3 : ℤ) ∣ 2 ^ a * (r.val : ℤ) - 1) (hq : q ≠ 1)
    (hy0 : 0 ≤ ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3)
    (hy : ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 ≤ ((offlawGrid 6198 : ℚ) : ℝ)) :
    jointContrib g Y q r k a = ⌊((2 : ℝ) ^ a)⁻¹ *
      (Y (q - 1) (childResidue a r)
        ⟨offlawIndex (((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3),
          Nat.lt_succ_of_le (offlawIndex_le _)⟩ : ℝ)⌋₊ := by
  rw [int_dvd_two_pow_mul_val_sub_one_iff] at h
  have hle : ¬ 2 ^ a * offlawGridNum k < 512 := by
    rw [← jointContrib_point_neg_iff]
    exact not_lt.2 hy0
  have hpt := jointContrib_point_of_le (not_lt.1 hle)
  have hnlt : ¬ 3 * 583351470707564294 < 2 ^ a * offlawGridNum k - 512 := by
    rw [not_lt, ← offlawGridNum_6198, ← natCast_div_le_offlawGrid_iff, ← hpt]
    exact hy
  have hidx : (⟨offlawIndex (((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3),
      Nat.lt_succ_of_le (offlawIndex_le _)⟩ : Fin 6199) =
      ⟨offlawIndexNum (2 ^ a * offlawGridNum k - 512), offlawIndexNum_lt _⟩ :=
    Fin.ext (by rw [Fin.val_mk, Fin.val_mk, hpt, offlawIndex_natCast_div])
  rw [hidx, inv_mul_eq_div, show (2 : ℝ) ^ a = ((2 ^ a : ℕ) : ℝ) by push_cast; rfl,
    Nat.floor_div_eq_div]
  simp [jointContrib, h, hq, hle, hnlt]

/-- Contribution of an in-range point at a level `q ≠ 1` from a verified grid index: if
`2^a r̃ % 3 = 1` and `p = 2^a n_k - 512` satisfies `3 n_j ≤ p ≤ 3 n_6198` and (`j = 6198` or
`p < 3 n_{j+1}`), then `c^{jt}_{g,𝖸}(q, r, k, a) = 𝖸_{q-1}(dn_a(r), j) / 2^a`. This checks a
claimed index by two comparisons instead of a scan. -/
theorem jointContrib_of_index (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ)
    {q : ℕ} (r : ResidueGroup q) {k a : ℕ} (j : Fin 6199) (h : 2 ^ a * r.val % 3 = 1)
    (hq : q ≠ 1) (hle : 512 ≤ 2 ^ a * offlawGridNum k)
    (hj : 3 * offlawGridNum j ≤ 2 ^ a * offlawGridNum k - 512)
    (hlast : 2 ^ a * offlawGridNum k - 512 ≤ 3 * 583351470707564294)
    (hnext : (j : ℕ) = 6198 ∨ 2 ^ a * offlawGridNum k - 512 < 3 * offlawGridNum ((j : ℕ) + 1)) :
    jointContrib g Y q r k a = Y (q - 1) (childResidue a r) j / 2 ^ a := by
  have hp : (0 : ℝ) ≤ ((2 ^ a * offlawGridNum k - 512 : ℕ) : ℝ) / 1536 :=
    div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hidx : offlawIndexNum (2 ^ a * offlawGridNum k - 512) = j := by
    rw [← offlawIndex_natCast_div]
    refine (offlawIndex_eq_iff hp).2 ⟨Nat.le_of_lt_succ j.2, ?_, ?_⟩
    · exact (offlawGrid_le_natCast_div_iff _ _).2 hj
    · rcases hnext with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge fun h' => absurd ((offlawGrid_le_natCast_div_iff _ _).1 h')
          (not_le.2 h))
  have hfin : (⟨offlawIndexNum (2 ^ a * offlawGridNum k - 512), offlawIndexNum_lt _⟩ :
      Fin 6199) = j := Fin.ext (by rw [Fin.val_mk]; exact hidx)
  simp only [jointContrib, h, ne_eq, not_true_eq_false, ite_false, hq, not_lt.2 hle,
    not_lt.2 hlast, hfin]

end CollatzPosDens
