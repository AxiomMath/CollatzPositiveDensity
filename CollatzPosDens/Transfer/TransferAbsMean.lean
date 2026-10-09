/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.GroupTheory.Index
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.LiftedTransfer
public import CollatzPosDens.Transfer.ResidueMapInjective
public import CollatzPosDens.Transfer.TransferMean

/-!
# The mean absolute value of a lifted transfer

Let `w` be a word of length `d`, `k ∈ ℕ`, `Q ≥ d + k` and `g : G_k → ℝ`. Then
`⟨|𝒯_{w,Q} g|⟩_Q = 2^{-A(w)} ⟨|g|⟩_k`.

Since the residue map `φ_w` is injective, each fiber of `φ_w` has at most one point, so
`|𝒯_w f| = 𝒯_w |f|` pointwise (the weight `ω(w)` being positive). The mean of a transfer then
gives `⟨𝒯_w |f|⟩_Q = 2^{-A(w)} ⟨|f|⟩_{Q-d}` for `f = g ∘ π_{Q-d,k}`, and since every fiber of the
reduction `π_{Q-d,k}` has exactly `3^{Q-d-k}` points, `⟨|f|⟩_{Q-d} = ⟨|g|⟩_k`.

## Main results

* `CollatzPosDens.abs_transfer`: `|𝒯_w g| = 𝒯_w |g|` pointwise.
* `CollatzPosDens.sum_comp_residueReduction`:
  `∑_{x ∈ G_q} F(π_{q,m} x) = 3^{q-m} ∑_{y ∈ G_m} F(y)`.
* `CollatzPosDens.residueAvg_comp_residueReduction`: `⟨F ∘ π_{q,m}⟩_q = ⟨F⟩_m`.
* `CollatzPosDens.residueAvg_liftedTransfer`: `⟨𝒯_{w,Q} g⟩_Q = 2^{-A(w)} ⟨g⟩_k`.
* `CollatzPosDens.residueAvg_abs_liftedTransfer`: `⟨|𝒯_{w,Q} g|⟩_Q = 2^{-A(w)} ⟨|g|⟩_k`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Since `φ_w` is injective and `ω(w) > 0`, the transfer commutes with absolute values:
`|(𝒯_w g)(y)| = (𝒯_w |g|)(y)`. -/
theorem abs_transfer (w : Word) {t : ℕ} (g : ResidueGroup t → ℝ)
    (y : ResidueGroup (t + w.length)) :
    |transfer w g y| = transfer w (fun z => |g z|) y := by
  have hω : (0 : ℝ) ≤ w.weight := by exact_mod_cast w.weight_pos.le
  rw [transfer_apply, transfer_apply, abs_mul, abs_of_nonneg hω]
  congr 1
  by_cases hy : ∃ z, residueMap w t z = y
  · obtain ⟨z, rfl⟩ := hy
    have hs : ({x | residueMap w t x = residueMap w t z} : Finset (ResidueGroup t)) = {z} := by
      ext x
      simp [(residueMap_injective w t).eq_iff]
    rw [hs, sum_singleton, sum_singleton]
  · push Not at hy
    have hs : ({x | residueMap w t x = y} : Finset (ResidueGroup t)) = ∅ := by
      ext x
      simp [hy x]
    rw [hs, sum_empty, sum_empty, abs_zero]

/-- Every fiber of the reduction `π_{q,m}` has `3^{q-m}` points, so
`∑_{x ∈ G_q} F(π_{q,m} x) = 3^{q-m} ∑_{y ∈ G_m} F(y)`. -/
theorem sum_comp_residueReduction {m q : ℕ} (h : m ≤ q) (F : ResidueGroup m → ℝ) :
    ∑ x, F (residueReduction h x) = (3 : ℝ) ^ (q - m) * ∑ y, F y := by
  set π := residueReduction h
  rw [← sum_fiberwise univ π (fun x => F (π x)), mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_congr rfl (g := fun _ => F y) (fun x hx => by rw [(mem_filter.mp hx).2]),
    sum_const, card_filter_residueReduction_eq, nsmul_eq_mul]
  push_cast
  rfl

/-- Pulling back along the reduction preserves averages: `⟨F ∘ π_{q,m}⟩_q = ⟨F⟩_m`. -/
theorem residueAvg_comp_residueReduction {m q : ℕ} (h : m ≤ q) (F : ResidueGroup m → ℝ) :
    residueAvg q (F ∘ residueReduction h) = residueAvg m F := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [residueAvg_def, residueAvg_def, Function.comp_def, sum_comp_residueReduction,
    Nat.add_sub_cancel_left, pow_add]
  field_simp

/-- The mean of a lifted transfer: for a word `w` of length `d`, `d + k ≤ Q` and
`g : G_k → ℝ`, `⟨𝒯_{w,Q} g⟩_Q = 2^{-A(w)} ⟨g⟩_k`. -/
theorem residueAvg_liftedTransfer (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q)
    (g : ResidueGroup k → ℝ) :
    residueAvg Q (liftedTransfer w h g) = (2 : ℝ) ^ (-(w.valSum : ℤ)) * residueAvg k g := by
  have hQ := Nat.sub_add_cancel (le_of_add_le_left h)
  have hbij : Function.Bijective (residueReduction hQ.le) := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨residueReduction hQ.ge, fun y => ?_, fun y => ?_⟩ <;>
      simp
  set f := g ∘ residueReduction (Nat.le_sub_of_add_le' h)
  have key : residueAvg Q (liftedTransfer w h g) =
      residueAvg (Q - w.length + w.length) (transfer w f) := by
    rw [residueAvg_def, residueAvg_def]
    congr 1
    · rw [hQ]
    simp only [liftedTransfer_apply]
    exact Function.Bijective.sum_comp hbij (transfer w f)
  rw [key, residueAvg_transfer, residueAvg_comp_residueReduction]

/-- The mean absolute value of a lifted transfer: for a word `w` of length `d`, `d + k ≤ Q` and
`g : G_k → ℝ`, `⟨|𝒯_{w,Q} g|⟩_Q = 2^{-A(w)} ⟨|g|⟩_k`. -/
@[collatz_pos_dens "lem_transfer_abs_mean"]
theorem residueAvg_abs_liftedTransfer (w : Word) {k Q : ℕ} (h : w.length + k ≤ Q)
    (g : ResidueGroup k → ℝ) :
    residueAvg Q (fun y => |liftedTransfer w h g y|) =
      (2 : ℝ) ^ (-(w.valSum : ℤ)) * residueAvg k (fun y => |g y|) := by
  have e : (fun y => |liftedTransfer w h g y|) = liftedTransfer w h (fun y => |g y|) := by
    funext y
    simp only [liftedTransfer_apply, abs_transfer]
    rfl
  rw [e, residueAvg_liftedTransfer]

end CollatzPosDens
