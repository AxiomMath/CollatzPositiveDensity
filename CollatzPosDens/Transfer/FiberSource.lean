/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.LinearCombination
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Maps.AffineIdentity
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Transfer.Transfer
public import CollatzPosDens.Transfer.LiftedTransfer

/-!
# The transfer at an integer point

Let `w` be a word of length `d`, `t ∈ ℕ` and `g : G_t → ℝ`. For an integer `R`, the fiber of the
residue map `φ_w : G_t → G_{t+d}` over `[R]_{t+d}` is the single point `[src(w, R)]_t` when `w`
is admissible from `R`, and is empty otherwise. Consequently
`(𝒯_w g)([R]_{t+d}) = ω(w) g([src(w, R)]_t)` if `w` is admissible from `R`, and `0` otherwise.

The proof writes `R = ω(w) src(w, R) + off(w)` (the affine identity). The number
`3^d src(w, R)` is always an integer `n`, and reducing the affine identity modulo `3^{t+d}`
shows that `φ_w(z) = [R]_{t+d}` holds exactly when `n ≡ 3^d z̃ (mod 3^{t+d})`, i.e. when
`src(w, R)` is an integer congruent to `z̃` modulo `3^t`. Each term `R_i` of the inverse orbit
is then a dyadic rational (by the affine identity for the suffix of `w`) with `3^i R_i ∈ ℤ`,
hence an integer, so `w` is admissible.

## Main results

* `CollatzPosDens.residueMap_eq_intCast_iff`: `φ_w(z) = [R]_{t+d}` iff `w` is admissible from
  `R` and `z = [src(w, R)]_t`.
* `CollatzPosDens.transfer_intCast`: the value of `𝒯_w g` at `[R]_{t+d}`.
* `CollatzPosDens.liftedTransfer_intCast`: the same for the lifted transfer at `[R]_Q`.

## Implementation notes

[mazur2026] takes `R` to be a positive odd integer; the statement holds for every integer `R`,
and is stated so. Since `src(w, R)` is a rational number, its reduction `[src(w, R)]_t` is
written as the reduction of its numerator, which is `src(w, R)` itself when `w` is admissible.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `3^k R` is an integer, then so is `3^{k+|w|} src(w, R)`. -/
private lemma exists_int_three_pow_mul_src_of_fiberSource (w : Word) :
    ∀ (k : ℕ) (R : ℚ) (n : ℤ), 3 ^ k * R = n →
      ∃ m : ℤ, (3 : ℚ) ^ (k + w.length) * src w R = m := by
  induction w with
  | nil => exact fun k R n h => ⟨n, by simpa using h⟩
  | cons a w ih =>
    intro k R n h
    obtain ⟨m, hm⟩ := ih (k + 1) (invStep a R) (2 ^ (a : ℕ) * n - 3 ^ k) (by
      rw [invStep]; push_cast; rw [← h]; ring)
    exact ⟨m, by rw [src_cons, List.length_cons, ← hm]; ring_nf⟩

/-- A dyadic rational `q` with `3^k q ∈ ℤ` is an integer. -/
private lemma den_eq_one_of_fiberSource {q : ℚ} (hq : q ∈ dyadicRationals) {k : ℕ} {n : ℤ}
    (h : 3 ^ k * q = n) : q.den = 1 := by
  obtain ⟨m, e, rfl⟩ := mem_dyadicRationals.1 hq
  have h2 : (2 : ℚ) ^ e ≠ 0 := by positivity
  have h' : (3 : ℤ) ^ k * m = 2 ^ e * n := by
    field_simp at h
    exact_mod_cast h
  have hcop : IsCoprime ((2 : ℤ) ^ e) ((3 : ℤ) ^ k) :=
    (Int.isCoprime_iff_gcd_eq_one.2 rfl).pow
  obtain ⟨c, rfl⟩ := hcop.dvd_of_dvd_mul_left ⟨n, h'⟩
  push_cast
  rw [mul_div_cancel_left₀ _ h2]
  exact Rat.den_intCast c

/-- If `φ_w(z) = [R]_{t+d}`, then `src(w, R)` is an integer of the form `z̃ - 3^t c`. -/
lemma exists_src_eq_of_residueMap_eq_intCast {w : Word} {t : ℕ} {R : ℤ} {z : ResidueGroup t}
    (h : residueMap w t z = (R : ResidueGroup (t + w.length))) :
    ∃ c : ℤ, src w R = ((z.val - 3 ^ t * c : ℤ) : ℚ) := by
  obtain ⟨n, hn⟩ := exists_int_three_pow_mul_src_of_fiberSource w 0 R R (by simp)
  rw [zero_add] at hn
  have hR : (R : ℚ) = n / 2 ^ w.valSum + off w := by
    conv_lhs => rw [eq_weight_mul_src_add_off w R]
    rw [Word.weight, div_mul_eq_mul_div, hn]
  have hd : (⟨(R : ℚ), by simp⟩ : dyadicRationals) =
      ⟨n / 2 ^ w.valSum, intCast_div_two_pow_mem n _⟩ + ⟨off w, off_mem_dyadicRationals w⟩ :=
    Subtype.ext hR
  have hK := congrArg (dyadicRed (t + w.length)) hd
  rw [map_add, dyadicRed_intCast, dyadicRed_div_two_pow] at hK
  rw [residueMap_apply, dyadicRed_weight, hK, add_left_inj] at h
  have h3 : ((3 ^ w.length * z.val - n : ℤ) : ResidueGroup (t + w.length)) = 0 := by
    push_cast
    linear_combination (2 : ResidueGroup (t + w.length)) ^ w.valSum * h -
      (3 ^ w.length * (z.val : ResidueGroup (t + w.length)) - n) *
        two_pow_mul_inv_two_pow (t + w.length) w.valSum
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h3
  have hc' : (3 : ℚ) ^ t * 3 ^ w.length * c = 3 ^ w.length * z.val - n := by
    rw [← pow_add]
    exact_mod_cast hc.symm
  refine ⟨c, mul_left_cancel₀ (pow_ne_zero w.length (three_ne_zero (α := ℚ))) ?_⟩
  rw [hn]
  push_cast
  linear_combination hc'

/-- If `src(w, R)` is an integer, then `w` is admissible from `R`. -/
lemma admissible_of_src_eq_intCast {w : Word} {R : ℤ} {s : ℤ} (hsrc : src w R = s) :
    Admissible R w := by
  intro i hi
  obtain ⟨m, hm⟩ := exists_int_three_pow_mul_src_of_fiberSource (w.take i) 0 R R (by simp)
  rw [List.length_take, min_eq_left hi, zero_add] at hm
  refine den_eq_one_of_fiberSource ?_ hm
  have he := eq_weight_mul_src_add_off (w.drop i) (inverseOrbit w R i)
  rw [inverseOrbit, ← src_append, List.take_append_drop, hsrc] at he
  rw [inverseOrbit, he]
  exact add_mem (mul_mem (Word.weight_mem_dyadicRationals _) (intCast_mem _ _))
    (off_mem_dyadicRationals _)

/-- If `w` is admissible from `R`, then `φ_w([src(w, R)]_t) = [R]_{t+d}`. -/
lemma residueMap_src_num_of_admissible {w : Word} {t : ℕ} {R : ℤ} (hadm : Admissible R w) :
    residueMap w t ((src w R).num : ResidueGroup t) = (R : ResidueGroup (t + w.length)) := by
  have hR := eq_weight_mul_src_add_off w R
  rw [← Rat.coe_int_num_of_den_eq_one hadm.den_src_eq_one] at hR
  have hd : (⟨(R : ℚ), by simp⟩ : dyadicRationals) =
      ⟨w.weight, w.weight_mem_dyadicRationals⟩ * ⟨((src w R).num : ℚ), by simp⟩ +
        ⟨off w, off_mem_dyadicRationals w⟩ :=
    Subtype.ext hR
  have hK := congrArg (dyadicRed (t + w.length)) hd
  rw [map_add, map_mul, dyadicRed_intCast, dyadicRed_intCast] at hK
  rw [residueMap_apply, hK, add_left_inj, dyadicRed_weight]
  set M := (src w R).num
  have hv : ((((M : ResidueGroup t).val : ℤ)) : ResidueGroup (t + w.length)) =
      M - 3 ^ t * ((M / 3 ^ t : ℤ) : ResidueGroup (t + w.length)) := by
    rw [ZMod.val_intCast, Int.emod_def]
    push_cast
    ring
  rw [Int.cast_natCast] at hv
  rw [hv]
  linear_combination (-(2⁻¹ ^ w.valSum * ((M / 3 ^ t : ℤ) : ResidueGroup (t + w.length)))) *
    three_pow_self_residueGroup (t + w.length)

/-- The fiber of the residue map `φ_w : G_t → G_{t+d}` over the reduction of an integer `R`:
`φ_w(z) = [R]_{t+d}` iff `w` is admissible from `R` and `z = [src(w, R)]_t`. -/
theorem residueMap_eq_intCast_iff (w : Word) (t : ℕ) (R : ℤ) (z : ResidueGroup t) :
    residueMap w t z = (R : ResidueGroup (t + w.length)) ↔
      Admissible R w ∧ ((src w R).num : ResidueGroup t) = z := by
  refine ⟨fun h => ?_, fun ⟨hadm, hz⟩ => hz ▸ residueMap_src_num_of_admissible hadm⟩
  obtain ⟨c, hsrc⟩ := exists_src_eq_of_residueMap_eq_intCast h
  refine ⟨admissible_of_src_eq_intCast hsrc, ?_⟩
  rw [hsrc, Rat.num_intCast]
  push_cast
  rw [three_pow_self_residueGroup, zero_mul, sub_zero, ZMod.natCast_zmod_val]

open Finset in
/-- The transfer `𝒯_w g` at the reduction `[R]_{t+d}` of an integer `R`: it equals
`ω(w) g([src(w, R)]_t)` if `w` is admissible from `R`, and `0` otherwise. -/
@[collatz_pos_dens "lem_fiber_source"]
theorem transfer_intCast (w : Word) {t : ℕ} (g : ResidueGroup t → ℝ) (R : ℤ) :
    transfer w g (R : ResidueGroup (t + w.length)) =
      if Admissible R w then (w.weight : ℝ) * g ((src w R).num : ResidueGroup t) else 0 := by
  rw [transfer_apply]
  split_ifs with h
  · have hs : ({z | residueMap w t z = (R : ResidueGroup (t + w.length))} : Finset _) =
        {((src w R).num : ResidueGroup t)} := by
      ext z
      simp [residueMap_eq_intCast_iff, h, eq_comm]
    rw [hs, sum_singleton]
  · rw [sum_eq_zero fun z hz => absurd ((residueMap_eq_intCast_iff w t R z).1
      (mem_filter.1 hz).2).1 h, mul_zero]

/-- The lifted transfer at the reduction `[R]_Q` of an integer `R`: it equals
`ω(w) g([src(w, R)]_k)` if `w` is admissible from `R`, and `0` otherwise. -/
theorem liftedTransfer_intCast (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q)
    (g : ResidueGroup k → ℝ) (R : ℤ) :
    liftedTransfer w h g (R : ResidueGroup Q) =
      if Admissible R w then (w.weight : ℝ) * g ((src w R).num : ResidueGroup k) else 0 := by
  rw [liftedTransfer_apply, residueReduction_intCast, transfer_intCast]
  simp only [Function.comp_apply, residueReduction_intCast]

end CollatzPosDens
