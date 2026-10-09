/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxOffsetLaw
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Transfer.Reduction
public import CollatzPosDens.Maps.Offset

/-!
# Pushforward of the reference law under reduction

For integers `0 ≤ m ≤ q` and `x ∈ G_m`, the reference law is compatible with the reduction
`π_{q,m} : G_q → G_m`:
$$\sum_{y \in G_q,\ \pi_{q,m}(y) = x} \mu_q(y) = \mu_m(x).$$

The map `π_{q,m} ∘ [·]_q : ℤ[1/2] → G_m` is a ring homomorphism, hence equals `[·]_m`. By
`refLaw_eq_tsum_off`, the left side is `∑_{w ∈ ℤ_{≥1}^q} 2^{-A(w)} [[off(w)]_m = x]`. Splitting
`w = uv` with `|u| = m`, `|v| = q - m`, the identity `off_append`,
`off(uv) = off(u) + 3^m 2^{-A(u)} off(v)`, gives `[off(w)]_m = [off(u)]_m`, and summing out `v`
with `𝐩(ℤ_{≥1}^{q-m}) = 1` leaves `μ_m(x)` by `refLaw_eq_tsum_off` again.

## Main results

* `CollatzPosDens.residueReduction_dyadicRed`: `π_{q,m}([x]_q) = [x]_m`.
* `CollatzPosDens.sum_refLaw_residueReduction_eq`:
  `∑_{y ∈ G_q, π_{q,m}(y) = x} μ_q(y) = μ_m(x)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Reduction commutes with the reduction of dyadic rationals: `π_{q,m}([x]_q) = [x]_m`. -/
theorem residueReduction_dyadicRed {m q : ℕ} (h : m ≤ q) (x : dyadicRationals) :
    residueReduction h (dyadicRed q x) = dyadicRed m x := by
  rw [← RingHom.comp_apply, eq_dyadicRed ((residueReduction h).comp (dyadicRed q))]

/-- Concatenation is a bijection `ℤ_{≥1}^m × ℤ_{≥1}^{q-m} ≃ ℤ_{≥1}^q` for `m ≤ q`. -/
private def mxPushforwardAppendEquiv {m q : ℕ} (h : m ≤ q) :
    {u : Word | u.length = m} × {v : Word | v.length = q - m} ≃
      {w : Word | w.length = q} where
  toFun p := ⟨p.1.1 ++ p.2.1, by
    have h1 := p.1.2; have h2 := p.2.2
    simp only [Set.mem_ofPred_eq] at h1 h2 ⊢
    rw [List.length_append, h1, h2]; omega⟩
  invFun w := (⟨w.1.take m, by
    have h1 := w.2; simp only [Set.mem_ofPred_eq] at h1 ⊢
    rw [List.length_take, h1]; omega⟩, ⟨w.1.drop m, by
    have h1 := w.2; simp only [Set.mem_ofPred_eq] at h1 ⊢
    rw [List.length_drop, h1]⟩)
  left_inv p := by
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
    simp only [Set.mem_ofPred_eq] at hu
    ext <;> simp [← hu]
  right_inv w := by
    ext1
    simp

/-- The offset of `uv` with `|u| = m` reduces modulo `3^m` like the offset of `u`. -/
private theorem dyadicRed_off_append_of_length {m : ℕ} (u v : Word) (hu : u.length = m) :
    dyadicRed m ⟨off (u ++ v), off_mem_dyadicRationals _⟩ =
      dyadicRed m ⟨off u, off_mem_dyadicRationals u⟩ := by
  rw [dyadicRed_off_append, dyadicRed_weight, hu, three_pow_self_residueGroup, zero_mul, zero_mul,
    add_zero]

/-- **Pushforward of the reference law.** For `m ≤ q` and `x ∈ G_m`,
`∑_{y ∈ G_q, π_{q,m}(y) = x} μ_q(y) = μ_m(x)`. -/
@[collatz_pos_dens "lem_mx_pushforward"]
theorem sum_refLaw_residueReduction_eq {m q : ℕ} (h : m ≤ q) (x : ResidueGroup m) :
    ∑ y ∈ univ.filter (fun y : ResidueGroup q => residueReduction h y = x), refLaw q y =
      refLaw m x := by
  have step1 : ∑ y ∈ univ.filter (fun y : ResidueGroup q => residueReduction h y = x),
      refLaw q y = ∑' w : {w : Word | w.length = q},
        if dyadicRed m ⟨off w.1, off_mem_dyadicRationals w.1⟩ = x then
          (2 ^ w.1.valSum)⁻¹ else 0 := by
    simp_rw [refLaw_eq_tsum_off]
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine tsum_congr fun w => ?_
    rw [Finset.sum_ite_eq]
    simp [residueReduction_dyadicRed]
  set g : Word → ℝ≥0∞ := fun w =>
    if dyadicRed m ⟨off w, off_mem_dyadicRationals w⟩ = x then (2 ^ w.valSum)⁻¹ else 0 with hg
  rw [step1, refLaw_eq_tsum_off m x]
  change ∑' w : {w : Word | w.length = q}, g w.1 = ∑' u : {u : Word | u.length = m}, g u.1
  rw [← (mxPushforwardAppendEquiv h).tsum_eq]
  change ∑' p : {u : Word | u.length = m} × {v : Word | v.length = q - m}, g (p.1.1 ++ p.2.1) = _
  rw [ENNReal.tsum_prod (f := fun (u : {u : Word | u.length = m})
    (v : {v : Word | v.length = q - m}) => g (u.1 ++ v.1))]
  refine tsum_congr fun ⟨u, hu⟩ => ?_
  simp only [Set.mem_ofPred_eq] at hu
  simp only [hg, dyadicRed_off_append_of_length u _ hu, Word.valSum_append, pow_add]
  split_ifs
  · have hv := geomMass_setOf_length_eq (q - m)
    rw [geomMass_def] at hv
    have key : ∀ a b : ℕ, ((2 : ℝ≥0∞) ^ a * 2 ^ b)⁻¹ = (2 ^ a)⁻¹ * 2⁻¹ ^ b := fun a b => by
      rw [ENNReal.mul_inv (by simp) (by simp), ← ENNReal.inv_pow (n := b)]
    simp only [key]
    rw [ENNReal.tsum_mul_left]
    simp only [Word.massWeight] at hv
    rw [hv, mul_one]
  · simp

end CollatzPosDens
