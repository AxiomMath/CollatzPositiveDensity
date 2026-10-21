/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05OfflawFloor
public import CollatzPosDens.Seed.S05OfflawIndex

/-!
# Integer contributions of an offset-law table

Let `g = (g_0, …, g_6198)` be a table of natural numbers, read as the step function
`2^{-62} g_{ι(y)}` on the offset grid `(ξ_k)`. For a grid index `k` and a letter `a ≥ 1`, the
one-letter recursion of the offset law evaluates the table at
$$y_{k,a} = \frac{2^a \xi_k - 1}{3}.$$
The *integer contribution* of the pair `(k, a)` is
$$c_g(k,a) = \begin{cases} 0 & y_{k,a} < 0,\\
  \bigl\lfloor 2^{-a} \lfloor 2^{62} \mathsf G_0(y_{k,a}) \rfloor \bigr\rfloor
    & y_{k,a} > \xi_{6198},\\
  \bigl\lfloor 2^{-a} g_{\iota(y_{k,a})} \bigr\rfloor & \text{otherwise,}\end{cases}$$
where `𝖦₀` is the tail floor `CollatzPosDens.offlawFloor` and `ι` the grid index
`CollatzPosDens.offlawIndex`.

Since `ξ_k = n_k / 512` with `n_k = offlawGridNum k ∈ ℕ`, the point `y_{k,a}` is the rational
number `(2^a n_k - 512) / 1536`. All three cases are therefore decided, and all three values
computed, in natural-number arithmetic: `y_{k,a} < 0` iff `2^a n_k < 512`; writing
`p = 2^a n_k - 512`, `y_{k,a} > ξ_6198` iff `3 n_6198 < p` (the numerator
`n_6198 = 583351470707564294` enters the definition as a literal), and `ξ_j ≤ y_{k,a}` iff
`3 n_j ≤ p`.

## Main definitions

* `CollatzPosDens.offlawContrib g k a`: the contribution `c_g(k,a) ∈ ℕ`, in natural-number
  arithmetic.
* `CollatzPosDens.offlawIndexNum p`: the grid index of `p / 1536`, in natural-number arithmetic.

## Main results

* `CollatzPosDens.offlawContrib_of_neg`, `CollatzPosDens.offlawContrib_of_lt`,
  `CollatzPosDens.offlawContrib_of_nonneg_of_le`: the three cases of `c_g(k,a)`, stated with the
  real point `y_{k,a}`, the tail floor `𝖦₀` and the grid index `ι`.
* `CollatzPosDens.offlawIndex_natCast_div`: `ι(p / 1536) = offlawIndexNum p`.
* `CollatzPosDens.offlawContrib_of_index`: the contribution of an in-range point, given a
  verified grid index, as `g_j / 2^a`.

## Implementation notes

The contribution is defined for all `k, a ∈ ℕ`; the ranges `k ≤ 6198` and `1 ≤ a ≤ 60` are
those used by the certificate and are not needed by the case lemmas. The table is a function
`Fin 6199 → ℕ`; the grid index is at most `6198`, so it is a valid argument.

The definition is the natural-number form, so that the kernel evaluates it on literals. The
grid index is a `Nat.findGreatest`, which the kernel evaluates by scanning the grid; for a
large certificate, `CollatzPosDens.offlawContrib_of_index` replaces that scan by checking a
claimed index `j` through two comparisons `3 n_j ≤ p < 3 n_{j+1}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.6.
-/
@[expose] public section

namespace CollatzPosDens

/-- The grid index of `p / 1536` in natural-number arithmetic: the largest `j ≤ 6198` with
`3 n_j ≤ p`, where `n_j = offlawGridNum j` (and `0` if there is none). -/
def offlawIndexNum (p : ℕ) : ℕ :=
  Nat.findGreatest (fun j => 3 * offlawGridNum j ≤ p) 6198

/-- The grid index `offlawIndexNum p` is at most `6198`. -/
theorem offlawIndexNum_le (p : ℕ) : offlawIndexNum p ≤ 6198 :=
  Nat.findGreatest_le _

/-- The grid index `offlawIndexNum p` is less than `6199`. -/
theorem offlawIndexNum_lt (p : ℕ) : offlawIndexNum p < 6199 :=
  Nat.lt_succ_of_le (offlawIndexNum_le p)

/-- **Integer contribution** `c_g(k,a)` of the pair `(k, a)` to an offset-law table `g`, with
`y_{k,a} = (2^a ξ_k - 1)/3 = (2^a n_k - 512)/1536`: it is `0` if `y_{k,a} < 0`,
`⌊2^{-a} ⌊2^62 𝖦₀(y_{k,a})⌋⌋` if `y_{k,a} > ξ_6198`, and `⌊2^{-a} g_{ι(y_{k,a})}⌋` otherwise.
Here `583351470707564294 = n_6198` (`offlawGridNum_6198`). The case lemmas
`offlawContrib_of_neg`, `offlawContrib_of_lt` and `offlawContrib_of_nonneg_of_le` state the three
cases with the real point `y_{k,a}`. -/
@[collatz_pos_dens "def_s05_offlaw_contrib"]
def offlawContrib (g : Fin 6199 → ℕ) (k a : ℕ) : ℕ :=
  if 2 ^ a * offlawGridNum k < 512 then 0
  else if 3 * 583351470707564294 < 2 ^ a * offlawGridNum k - 512 then
    offlawFloorNum 62 (2 ^ a * offlawGridNum k - 512) 1536 / 2 ^ a
  else g ⟨offlawIndexNum (2 ^ a * offlawGridNum k - 512), offlawIndexNum_lt _⟩ / 2 ^ a

/-- The point `y_{k,a} = (2^a ξ_k - 1)/3` is `(2^a n_k - 512)/1536` in real form. -/
private theorem offlawContrib_point (k a : ℕ) :
    ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 =
      ((2 ^ a * offlawGridNum k : ℕ) - 512 : ℝ) / 1536 := by
  rw [offlawGrid_eq_offlawGridNum]
  push_cast
  ring

/-- For `512 ≤ 2^a n_k`, `y_{k,a} = p / 1536` with `p = 2^a n_k - 512`. -/
private theorem offlawContrib_point_of_le {k a : ℕ} (h : 512 ≤ 2 ^ a * offlawGridNum k) :
    ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 =
      ((2 ^ a * offlawGridNum k - 512 : ℕ) : ℝ) / 1536 := by
  rw [offlawContrib_point, Nat.cast_sub h]
  norm_num

/-- `512 ≤ 2^a n_k` as soon as `y_{k,a} ≥ 0`. -/
private theorem le_of_offlawContrib_point_nonneg {k a : ℕ}
    (hy : 0 ≤ ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3) :
    512 ≤ 2 ^ a * offlawGridNum k := by
  by_contra h
  rw [offlawContrib_point] at hy
  have h' : ((2 ^ a * offlawGridNum k : ℕ) : ℝ) < 512 := by exact_mod_cast not_le.1 h
  have : ((2 ^ a * offlawGridNum k : ℕ) - 512 : ℝ) / 1536 < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by norm_num)
  linarith

/-- `ξ_j ≤ p / 1536` iff `3 n_j ≤ p`. -/
theorem offlawGrid_le_natCast_div_iff (j p : ℕ) :
    ((offlawGrid j : ℚ) : ℝ) ≤ (p : ℝ) / 1536 ↔ 3 * offlawGridNum j ≤ p := by
  rw [offlawGrid_eq_offlawGridNum, ← @Nat.cast_le ℝ]
  push_cast
  constructor <;> intro h <;> linarith

/-- `p / 1536 ≤ ξ_j` iff `p ≤ 3 n_j`. -/
theorem natCast_div_le_offlawGrid_iff (j p : ℕ) :
    (p : ℝ) / 1536 ≤ ((offlawGrid j : ℚ) : ℝ) ↔ p ≤ 3 * offlawGridNum j := by
  rw [offlawGrid_eq_offlawGridNum, ← @Nat.cast_le ℝ]
  push_cast
  constructor <;> intro h <;> linarith

/-- The grid index of `p / 1536` is `offlawIndexNum p`. -/
theorem offlawIndex_natCast_div (p : ℕ) : offlawIndex ((p : ℝ) / 1536) = offlawIndexNum p := by
  have hp : (0 : ℝ) ≤ (p : ℝ) / 1536 := by positivity
  rw [offlawIndex_eq_iff hp]
  refine ⟨offlawIndexNum_le p, ?_, ?_⟩
  · rw [offlawGrid_le_natCast_div_iff]
    exact Nat.findGreatest_spec (P := fun j => 3 * offlawGridNum j ≤ p) (Nat.zero_le _)
      (by simp [offlawGridNum])
  · rcases (offlawIndexNum_le p).lt_or_eq with h | h
    · right
      rw [← not_le, offlawGrid_le_natCast_div_iff]
      exact Nat.findGreatest_is_greatest (P := fun j => 3 * offlawGridNum j ≤ p)
        (Nat.lt_succ_self _) (Nat.succ_le_of_lt h)
    · exact Or.inl h

/-- **First case of `c_g(k,a)`**: if `y_{k,a} = (2^a ξ_k - 1)/3 < 0`, then `c_g(k,a) = 0`. -/
@[collatz_pos_dens "def_s05_offlaw_contrib"]
theorem offlawContrib_of_neg (g : Fin 6199 → ℕ) {k a : ℕ}
    (hy : ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 < 0) :
    offlawContrib g k a = 0 := by
  have h : 2 ^ a * offlawGridNum k < 512 := by
    by_contra h
    rw [offlawContrib_point_of_le (not_lt.1 h)] at hy
    have : (0 : ℝ) ≤ ((2 ^ a * offlawGridNum k - 512 : ℕ) : ℝ) / 1536 := by positivity
    linarith
  rw [offlawContrib, ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- **Second case of `c_g(k,a)`**: if `y_{k,a} = (2^a ξ_k - 1)/3 > ξ_6198`, then
`c_g(k,a) = ⌊2^{-a} ⌊2^62 𝖦₀(y_{k,a})⌋⌋`. -/
@[collatz_pos_dens "def_s05_offlaw_contrib"]
theorem offlawContrib_of_lt (g : Fin 6199 → ℕ) {k a : ℕ}
    (hy : ((offlawGrid 6198 : ℚ) : ℝ) < ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3) :
    offlawContrib g k a = ⌊((2 : ℝ) ^ a)⁻¹ *
      ⌊(2 : ℝ) ^ 62 * offlawFloor (((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3)⌋₊⌋₊ := by
  have h0 : (0 : ℝ) ≤ ((offlawGrid 6198 : ℚ) : ℝ) := by exact_mod_cast offlawGrid_nonneg 6198
  have hle := le_of_offlawContrib_point_nonneg (k := k) (a := a) (by linarith)
  rw [offlawContrib_point_of_le hle] at hy ⊢
  have hlt : 3 * 583351470707564294 < 2 ^ a * offlawGridNum k - 512 := by
    rw [← offlawGridNum_6198, ← not_le, ← natCast_div_le_offlawGrid_iff]
    exact not_le.2 hy
  have hfl := floor_two_pow_mul_offlawFloor_natCast_div 62 (2 ^ a * offlawGridNum k - 512)
    (d := 1536) (by norm_num)
  push_cast at hfl
  rw [offlawContrib, ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hle)),
    ite_eq_left_of_eq_true _ _ (eq_true hlt), hfl, inv_mul_eq_div,
    show (2 : ℝ) ^ a = ((2 ^ a : ℕ) : ℝ) by push_cast; rfl, Nat.floor_div_eq_div]

/-- **Third case of `c_g(k,a)`**: if `0 ≤ y_{k,a} ≤ ξ_6198`, with `y_{k,a} = (2^a ξ_k - 1)/3`,
then `c_g(k,a) = ⌊2^{-a} g_{ι(y_{k,a})}⌋`. -/
@[collatz_pos_dens "def_s05_offlaw_contrib"]
theorem offlawContrib_of_nonneg_of_le (g : Fin 6199 → ℕ) {k a : ℕ}
    (hy0 : 0 ≤ ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3)
    (hy : ((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3 ≤ ((offlawGrid 6198 : ℚ) : ℝ)) :
    offlawContrib g k a = ⌊((2 : ℝ) ^ a)⁻¹ *
      (g ⟨offlawIndex (((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3),
        Nat.lt_succ_of_le (offlawIndex_le _)⟩ : ℝ)⌋₊ := by
  have hle := le_of_offlawContrib_point_nonneg hy0
  have hpt := offlawContrib_point_of_le hle
  have hnlt : ¬ 3 * 583351470707564294 < 2 ^ a * offlawGridNum k - 512 := by
    rw [not_lt, ← offlawGridNum_6198, ← natCast_div_le_offlawGrid_iff, ← hpt]
    exact hy
  have hidx : (⟨offlawIndex (((2 : ℝ) ^ a * ((offlawGrid k : ℚ) : ℝ) - 1) / 3),
      Nat.lt_succ_of_le (offlawIndex_le _)⟩ : Fin 6199) =
      ⟨offlawIndexNum (2 ^ a * offlawGridNum k - 512), offlawIndexNum_lt _⟩ :=
    Fin.ext (by rw [Fin.val_mk, Fin.val_mk, hpt, offlawIndex_natCast_div])
  rw [hidx, offlawContrib, ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hle)),
    ite_eq_right_of_eq_false _ _ (eq_false hnlt), inv_mul_eq_div,
    show (2 : ℝ) ^ a = ((2 ^ a : ℕ) : ℝ) by push_cast; rfl, Nat.floor_div_eq_div]

/-- Contribution of an in-range point from a verified grid index: if `p = 2^a n_k - 512`
satisfies `3 n_j ≤ p ≤ 3 n_6198` and (`j = 6198` or `p < 3 n_{j+1}`), then
`c_g(k,a) = g_j / 2^a`. -/
theorem offlawContrib_of_index (g : Fin 6199 → ℕ) {k a : ℕ} (j : Fin 6199)
    (hle : 512 ≤ 2 ^ a * offlawGridNum k)
    (hj : 3 * offlawGridNum j ≤ 2 ^ a * offlawGridNum k - 512)
    (hlast : 2 ^ a * offlawGridNum k - 512 ≤ 3 * 583351470707564294)
    (hnext : (j : ℕ) = 6198 ∨ 2 ^ a * offlawGridNum k - 512 < 3 * offlawGridNum ((j : ℕ) + 1)) :
    offlawContrib g k a = g j / 2 ^ a := by
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
  rw [offlawContrib, ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hle)),
    ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hlast)), hfin]

end CollatzPosDens
