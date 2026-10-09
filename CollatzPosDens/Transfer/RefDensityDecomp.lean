/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Transfer.RefDensityExt
public import CollatzPosDens.Transfer.TransferConcat

/-!
# Decomposition of the reference density over words

Write `G_Q` for the residue group `ResidueGroup Q`, `ρ_Q` for the reference density
`refDensity Q` on it, and `𝒯_w` for the transfer operator `transfer w` of a word `w`, with
residue map `φ_w = residueMap w` and weight `ω(w) = w.weight`. For integers `0 ≤ d ≤ Q` and
every `y ∈ G_Q`, `ρ_Q(y) = ∑_{w ∈ ℤ_{≥1}^d} (𝒯_w ρ_{Q-d})(y)`, the sum being taken in `[0, ∞]`.

The case `d = 1` is the recursion of the reference law: for a one-letter word `(a)` the
residue map is `φ_{(a)}(z) = [2^{-a}(3 z̃ + 1)]_{p+1}` and `ω((a)) = 3 · 2^{-a}`, so
`∑_{a ≥ 1} (𝒯_{(a)} ρ_p)(y) = ρ_{p+1}(y)`. The general case follows by induction on `d`,
using `𝒯_{(a)} 𝒯_{w'} = 𝒯_{(a) w'}` and the bijection `(a, w') ↦ (a) w'` from
`ℤ_{≥1} × ℤ_{≥1}^{d-1}` onto `ℤ_{≥1}^d`.

## Main results

* `CollatzPosDens.residueMap_singleton`: `φ_{(a)}(z) = [2^{-a}(3 z̃ + 1)]_{p+1}`.
* `CollatzPosDens.ofReal_refDensity_succ`: `ρ_{p+1}(y) = ∑_{a ≥ 1} (𝒯_{(a)} ρ_p)(y)`.
* `CollatzPosDens.ofReal_refDensity_add_eq_tsum_transfer`:
  `ρ_{t+d}(y) = ∑_{w ∈ ℤ_{≥1}^d} (𝒯_w ρ_t)(y)`.
* `CollatzPosDens.ofReal_refDensity_eq_tsum_transfer`: the statement for `0 ≤ d ≤ Q`.

## Implementation notes

The real numbers `ρ_Q(y) ≥ 0` and `(𝒯_w ρ_{Q-d})(y) ≥ 0` are embedded in `[0, ∞]` by
`ENNReal.ofReal`, and `ℤ_{≥1}^d` is the set of words of length `d`. The transfer
`𝒯_w ρ_{Q-d}` is a function on `G_{Q-d+|w|}`, and `Q - d + |w| = Q` only propositionally, so
the point `y ∈ G_Q` is transported along this equality with `cast`, which on `ZMod (3 ^ k)`
does not change the residue. The proof is first carried out for `Q = t + d`.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The transfer of a nonnegative function, read in `[0, ∞]`:
`(𝒯_w g)(y) = ω(w) ∑_{φ_w(z) = y} g(z)`. -/
theorem ofReal_transfer (w : Word) {t : ℕ} {g : ResidueGroup t → ℝ} (hg : 0 ≤ g)
    (y : ResidueGroup (t + w.length)) :
    ENNReal.ofReal (transfer w g y) =
      ENNReal.ofReal (w.weight : ℝ) * ∑ z with residueMap w t z = y, ENNReal.ofReal (g z) := by
  rw [transfer_apply, ENNReal.ofReal_mul (by exact_mod_cast w.weight_pos.le),
    ENNReal.ofReal_sum_of_nonneg fun z _ => hg z]

/-- The residue map of a one-letter word is the Syracuse step:
`φ_{(a)}(z) = [2^{-a}(3 z̃ + 1)]_{p+1}`. -/
theorem residueMap_singleton (a : ℕ+) {p : ℕ} (z : ResidueGroup p) :
    residueMap [a] p z = refStep p a z := by
  have h0 : (⟨off [a], off_mem_dyadicRationals [a]⟩ : dyadicRationals) =
      ⟨((1 : ℤ) : ℚ) / 2 ^ (a : ℕ), intCast_div_two_pow_mem 1 a⟩ :=
    Subtype.ext (by simp [div_eq_inv_mul])
  rw [residueMap_apply, dyadicRed_weight, refStep_eq, h0, dyadicRed_div_two_pow]
  simp only [Word.valSum_singleton, List.length_singleton, pow_one, Int.cast_one]
  ring

/-- One step of the decomposition: `ρ_{p+1}(y) = ∑_{a ≥ 1} (𝒯_{(a)} ρ_p)(y)` in `[0, ∞]`. -/
theorem ofReal_refDensity_succ (p : ℕ) (y : ResidueGroup (p + 1)) :
    ENNReal.ofReal (refDensity (p + 1) y) =
      ∑' a : ℕ+, ENNReal.ofReal (transfer [a] (refDensity p) y) := by
  have key (a : ℕ+) : ENNReal.ofReal (transfer [a] (refDensity p) y) =
      2 / 3 * 3 ^ (p + 1) * (2⁻¹ ^ (a : ℕ) *
        ∑ z ∈ univ.filter (fun z => refStep p a z = y), refLaw p z) := by
    rw [ofReal_transfer _ (fun z => refDensity_nonneg p z)]
    simp only [residueMap_singleton, ← refLaw_mul_eq_ofReal_refDensity, ← mul_sum,
      Word.weight_singleton]
    rw [Rat.cast_div, Rat.cast_pow, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.div_eq_inv_mul, ← ENNReal.inv_pow]
    norm_num
    ring
  rw [tsum_congr key, ← refLaw_mul_eq_ofReal_refDensity, refLaw_succ_apply,
    ENNReal.tsum_mul_left, tsum_pnat_eq_tsum_succ
      (f := fun a => 2⁻¹ ^ a * ∑ z ∈ univ.filter (fun z => refStep p a z = y), refLaw p z)]

/-- The decomposition of `ρ_{t+d}` over the words of length `d`:
`ρ_{t+d}(y) = ∑_{w ∈ ℤ_{≥1}^d} (𝒯_w ρ_t)(y)` in `[0, ∞]`, for `y ∈ G_{t+d}`. -/
theorem ofReal_refDensity_add_eq_tsum_transfer (t d : ℕ) (y : ResidueGroup (t + d)) :
    ENNReal.ofReal (refDensity (t + d) y) =
      ∑' w : {w : Word | w.length = d}, ENNReal.ofReal (transfer w.1 (refDensity t)
        (cast (congrArg (fun k => ResidueGroup (t + k)) w.2.symm) y)) := by
  induction d with
  | zero =>
    rw [tsum_eq_single (⟨[], rfl⟩ : {w : Word | w.length = 0})]
    · simp [transfer_apply, Finset.filter_eq']
    · rintro ⟨w, hw⟩ hne
      exact absurd (Subtype.ext (List.eq_nil_of_length_eq_zero hw)) hne
  | succ d ih =>
    change ENNReal.ofReal (refDensity (t + d + 1) y) = _
    rw [ofReal_refDensity_succ, ← (Word.consLengthEquiv d).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun a => ?_
    rw [ofReal_transfer _ (fun z => refDensity_nonneg _ z)]
    simp_rw [ih]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
    refine tsum_congr fun ⟨w', hw'⟩ => ?_
    subst hw'
    simp only [cast_eq]
    rw [← ofReal_transfer _ (transfer_nonneg _ (fun z => refDensity_nonneg _ z)),
      ← transfer_append]
    rfl

/-- **Decomposition of the reference density.** For integers `0 ≤ d ≤ Q` and every
`y ∈ G_Q`, `ρ_Q(y) = ∑_{w ∈ ℤ_{≥1}^d} (𝒯_w ρ_{Q-d})(y)`, the sum of the nonnegative reals
`(𝒯_w ρ_{Q-d})(y)` being taken in `[0, ∞]`. Here `y` is read in `G_{Q-d+|w|} = G_Q`. -/
@[collatz_pos_dens "lem_ref_density_decomp"]
theorem ofReal_refDensity_eq_tsum_transfer {Q d : ℕ} (hd : d ≤ Q) (y : ResidueGroup Q) :
    ENNReal.ofReal (refDensity Q y) =
      ∑' w : {w : Word | w.length = d}, ENNReal.ofReal (transfer w.1 (refDensity (Q - d))
        (cast (congrArg ResidueGroup (by rw [w.2, Nat.sub_add_cancel hd])) y)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hd
  rw [ofReal_refDensity_add_eq_tsum_transfer t d y]
  refine tsum_congr fun w => ?_
  have key : ∀ s (hs : s = t) h, transfer w.1 (refDensity s) (cast h y) =
      transfer w.1 (refDensity t)
        (cast (congrArg (fun k => ResidueGroup (t + k)) w.2.symm) y) := by
    rintro s rfl h
    rfl
  rw [key _ (Nat.add_sub_cancel t d)]

end CollatzPosDens
