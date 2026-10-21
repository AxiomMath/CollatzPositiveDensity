/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05OfflawGrid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# The tail floor of the offset law

The *tail floor* of the offset law is the explicit function
$$\mathsf G_0(x) = \max\Bigl(0,\ 1 - \frac{7}{x+2}\Bigr), \qquad x \ge 0 .$$
It vanishes on `[0, 5]`, equals `(x - 5)/(x + 2)` for `x ≥ 5`, takes values in `[0, 1)` and is
nondecreasing on `[0, ∞)`. At a nonnegative rational point `p/d` it is the rational number
`(p - 5d)⁺ / (p + 2d)`, so its scaled floors `⌊2^e 𝖦₀(p/d)⌋` are natural-number quotients.

## Main definitions

* `CollatzPosDens.offlawFloor x`: the tail floor `𝖦₀(x) ∈ ℝ`.
* `CollatzPosDens.offlawFloorNum e p d`: the natural number `2^e (p - 5d) / (p + 2d)`, which is
  `⌊2^e 𝖦₀(p/d)⌋`.

## Main results

* `CollatzPosDens.offlawFloor_nonneg`, `CollatzPosDens.offlawFloor_lt_one`: `0 ≤ 𝖦₀(x) < 1` for
  `x ≥ 0`.
* `CollatzPosDens.offlawFloor_monotoneOn`: `𝖦₀` is nondecreasing on `[0, ∞)`.
* `CollatzPosDens.offlawFloor_eq_zero`, `CollatzPosDens.offlawFloor_of_five_le`: `𝖦₀ = 0` on
  `[0, 5]` and `𝖦₀(x) = (x - 5)/(x + 2)` for `x ≥ 5`.
* `CollatzPosDens.offlawFloor_natCast_div`: `𝖦₀(p/d) = (p - 5d)/(p + 2d)` (truncated subtraction).
* `CollatzPosDens.floor_two_pow_mul_offlawFloor_natCast_div`:
  `⌊2^e 𝖦₀(p/d)⌋₊ = offlawFloorNum e p d`.
* `CollatzPosDens.floor_two_pow_mul_offlawFloor_offlawGrid`: at a grid point `ξ_k = n_k/512`,
  `⌊2^e 𝖦₀(ξ_k)⌋₊ = 2^e (n_k - 2560)/(n_k + 1024)`, with `n_k = offlawGridNum k`.

## Implementation notes

`offlawFloor` is defined on all of `ℝ`; the hypothesis `x ≥ 0` of the definition is carried by
the lemmas that need it. The natural-number form `offlawFloorNum` uses only `Nat` subtraction,
multiplication, power and division, so the kernel evaluates it directly on binary literals.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Tail floor of the offset law**: `𝖦₀(x) = max(0, 1 - 7/(x + 2))`, used for `x ≥ 0`. -/
@[collatz_pos_dens "def_s05_offlaw_floor"]
noncomputable def offlawFloor (x : ℝ) : ℝ :=
  max 0 (1 - 7 / (x + 2))

/-- The natural number `2^e (p - 5d) / (p + 2d)`, equal to `⌊2^e 𝖦₀(p/d)⌋` for `d > 0`. -/
def offlawFloorNum (e p d : ℕ) : ℕ :=
  2 ^ e * (p - 5 * d) / (p + 2 * d)

/-- `𝖦₀(x) ≥ 0` for every real `x`. -/
theorem offlawFloor_nonneg (x : ℝ) : 0 ≤ offlawFloor x :=
  le_max_left _ _

/-- `𝖦₀(x) < 1` for `x ≥ 0`. -/
theorem offlawFloor_lt_one {x : ℝ} (hx : 0 ≤ x) : offlawFloor x < 1 := by
  have : 0 < 7 / (x + 2) := by positivity
  exact max_lt (by norm_num) (by linarith)

/-- `𝖦₀(x) ≤ 1` for `x ≥ 0`. -/
theorem offlawFloor_le_one {x : ℝ} (hx : 0 ≤ x) : offlawFloor x ≤ 1 :=
  (offlawFloor_lt_one hx).le

/-- `𝖦₀(x) = (x - 5)/(x + 2)` for `x ≥ 5`. -/
theorem offlawFloor_of_five_le {x : ℝ} (hx : 5 ≤ x) : offlawFloor x = (x - 5) / (x + 2) := by
  have h2 : x + 2 ≠ 0 := by linarith
  have : 1 - 7 / (x + 2) = (x - 5) / (x + 2) := by field_simp; ring
  rw [offlawFloor, this, max_eq_right (div_nonneg (by linarith) (by linarith))]

/-- `𝖦₀` vanishes on `(-2, 5]`, in particular on `[0, 5]`. -/
theorem offlawFloor_eq_zero {x : ℝ} (hx0 : -2 < x) (hx : x ≤ 5) : offlawFloor x = 0 := by
  have h7 : 1 ≤ 7 / (x + 2) := by rw [le_div_iff₀ (by linarith)]; linarith
  exact max_eq_left (by linarith)

/-- `𝖦₀` is nondecreasing on `(-2, ∞)`. -/
theorem offlawFloor_monotoneOn_Ioi : MonotoneOn offlawFloor (Set.Ioi (-2)) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  have : 7 / (y + 2) ≤ 7 / (x + 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  exact max_le_max le_rfl (by linarith)

/-- `𝖦₀` is nondecreasing on `[0, ∞)`. -/
theorem offlawFloor_monotoneOn : MonotoneOn offlawFloor (Set.Ici 0) :=
  offlawFloor_monotoneOn_Ioi.mono fun x (hx : 0 ≤ x) => show -2 < x by linarith

/-- At a nonnegative rational point, `𝖦₀(p/d) = (p - 5d)/(p + 2d)` with truncated subtraction. -/
theorem offlawFloor_natCast_div (p : ℕ) {d : ℕ} (hd : 0 < d) :
    offlawFloor ((p : ℝ) / d) = ((p - 5 * d : ℕ) : ℝ) / ((p + 2 * d : ℕ) : ℝ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rcases le_or_gt (5 * d) p with h | h
  · rw [offlawFloor_of_five_le (by rw [le_div_iff₀ hd']; exact_mod_cast h),
      Nat.cast_sub h]
    push_cast
    field_simp
  · have hp : (0 : ℝ) ≤ p / d := by positivity
    rw [offlawFloor_eq_zero (by linarith) (by rw [div_le_iff₀ hd']; exact_mod_cast h.le),
      Nat.sub_eq_zero_of_le h.le]
    simp

/-- `⌊2^e 𝖦₀(p/d)⌋₊ = 2^e (p - 5d) / (p + 2d)` for `d > 0`. -/
theorem floor_two_pow_mul_offlawFloor_natCast_div (e p : ℕ) {d : ℕ} (hd : 0 < d) :
    ⌊(2 : ℝ) ^ e * offlawFloor ((p : ℝ) / d)⌋₊ = offlawFloorNum e p d := by
  rw [offlawFloor_natCast_div p hd, ← mul_div_assoc, offlawFloorNum,
    ← Nat.floor_div_eq_div (K := ℝ)]
  push_cast
  rfl

/-- At a grid point `ξ_k = n_k/512` (`n_k = offlawGridNum k`), the scaled floor is
`⌊2^e 𝖦₀(ξ_k)⌋₊ = 2^e (n_k - 2560)/(n_k + 1024)`. -/
theorem floor_two_pow_mul_offlawFloor_offlawGrid (e k : ℕ) :
    ⌊(2 : ℝ) ^ e * offlawFloor (offlawGrid k)⌋₊ = offlawFloorNum e (offlawGridNum k) 512 := by
  rw [← floor_two_pow_mul_offlawFloor_natCast_div e _ (by norm_num : 0 < 512),
    offlawGrid_eq_offlawGridNum]
  push_cast
  rfl

end CollatzPosDens
