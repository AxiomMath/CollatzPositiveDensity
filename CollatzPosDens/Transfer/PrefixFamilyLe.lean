/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.InformationTheory.Coding.PrefixFree
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RefDensityDecomp

/-!
# Transfers along a prefix-disjoint family are dominated by the reference density

Let `𝒱` be a finite prefix-disjoint set of words, all of length at most `h`, and let `Q ≥ h`.
Then for every `y ∈ G_Q`, `∑_{w ∈ 𝒱} (𝒯_w ρ_{Q-|w|})(y) ≤ ρ_Q(y)`.

Write `Q = t + h`. For `w ∈ 𝒱`, decomposing `ρ_{t + (h - |w|)}` over the words `v` of length
`h - |w|` and using `𝒯_w 𝒯_v = 𝒯_{wv}` gives `𝒯_w ρ_{Q-|w|} = ∑_v 𝒯_{wv} ρ_t` in `[0, ∞]`.
Concatenation `(w, v) ↦ wv` is injective by prefix-disjointness, so the left side is a
sub-sum of `∑_{u ∈ ℤ_{≥1}^h} (𝒯_u ρ_t)(y) = ρ_Q(y)`.

## Main results

* `CollatzPosDens.ofReal_transfer_refDensity_add_eq_tsum`:
  `(𝒯_w ρ_{t+d})(y) = ∑_{v ∈ ℤ_{≥1}^d} (𝒯_{wv} ρ_t)(y)` in `[0, ∞]`.
* `CollatzPosDens.sum_transfer_refDensity_le`: the inequality for a prefix-disjoint family.

## Implementation notes

Prefix-disjointness is Mathlib's `InformationTheory.IsPrefixFree`. The transfer
`𝒯_w ρ_{Q-|w|}` is a function on `G_{Q-|w|+|w|}`, which equals `G_Q` when `|w| ≤ Q` but only
propositionally; the point `y ∈ G_Q` is read there through `ZMod.cast`, which between rings
`ZMod (3 ^ k)` with equal moduli is the identity. This avoids a dependence of the summand
on a proof of `|w| ≤ Q`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.3.
-/

open scoped ENNReal
open InformationTheory

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Between residue groups of equal level, `ZMod.cast` is transport along the equality. -/
private theorem prefixFamilyLe_cast_eq_zmodCast {a b : ℕ} (hab : a = b) (y : ResidueGroup a) :
    cast (congrArg ResidueGroup hab) y = (y.cast : ResidueGroup b) := by
  subst hab
  simp [ZMod.cast_id]

/-- Transfers of the reference density along words extending `w`: for `y ∈ G_{t+d+|w|}`,
`(𝒯_w ρ_{t+d})(y) = ∑_{v ∈ ℤ_{≥1}^d} (𝒯_{wv} ρ_t)(y)` in `[0, ∞]`. -/
theorem ofReal_transfer_refDensity_add_eq_tsum (w : Word) (t d : ℕ)
    (y : ResidueGroup (t + d + w.length)) :
    ENNReal.ofReal (transfer w (refDensity (t + d)) y) =
      ∑' v : {v : Word | v.length = d}, ENNReal.ofReal (transfer (w ++ v.1) (refDensity t)
        (cast (congrArg ResidueGroup (by rw [List.length_append, v.2]; ring)) y)) := by
  rw [ofReal_transfer _ (fun z => refDensity_nonneg _ z)]
  simp_rw [ofReal_refDensity_add_eq_tsum_transfer]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun ⟨v, hv⟩ => ?_
  subst hv
  simp only [cast_eq]
  rw [← ofReal_transfer _ (transfer_nonneg _ (fun z => refDensity_nonneg _ z)),
    ← transfer_append]

/-- Concatenation `(w, v) ↦ wv`, from pairs of a word `w ∈ 𝒱` and a word of length
`h - |w|`, to the words of length `h`. -/
private def prefixFamilyLeConcat (V : Finset Word) (h : ℕ) (hlen : ∀ w ∈ V, w.length ≤ h) :
    (Σ w : V, {v : Word | v.length = h - (w : Word).length}) → {u : Word | u.length = h} :=
  fun p => ⟨(p.1 : Word) ++ p.2.1, by
    have := hlen _ p.1.2
    have h2 : p.2.1.length = h - (p.1 : Word).length := p.2.2
    simp only [Set.mem_ofPred_eq, List.length_append, h2]
    omega⟩

/-- Concatenation is injective on a prefix-disjoint family: two prefixes of one word are
comparable. -/
private theorem prefixFamilyLeConcat_injective {V : Finset Word}
    (hV : IsPrefixFree (V : Set Word)) (h : ℕ) (hlen : ∀ w ∈ V, w.length ≤ h) :
    Function.Injective (prefixFamilyLeConcat V h hlen) := by
  rintro ⟨⟨w₁, hw₁⟩, ⟨v₁, hv₁⟩⟩ ⟨⟨w₂, hw₂⟩, ⟨v₂, hv₂⟩⟩ heq
  simp only [prefixFamilyLeConcat, Subtype.mk.injEq] at heq
  have hp₁ : w₁ <+: w₂ ++ v₂ := heq ▸ List.prefix_append _ _
  have hp₂ : w₂ <+: w₂ ++ v₂ := List.prefix_append _ _
  have hw : w₁ = w₂ := by
    rcases le_total w₁.length w₂.length with hl | hl
    · exact hV _ hw₁ _ hw₂ (List.prefix_of_prefix_length_le hp₁ hp₂ hl)
    · exact (hV _ hw₂ _ hw₁ (List.prefix_of_prefix_length_le hp₂ hp₁ hl)).symm
  subst hw
  have hv : v₁ = v₂ := List.append_cancel_left heq
  subst hv
  rfl

/-- **Transfers along a prefix-disjoint family.** Let `𝒱` be a finite prefix-disjoint set of
words, all of length at most `h`, and let `Q ≥ h`. Then for every `y ∈ G_Q`,
`∑_{w ∈ 𝒱} (𝒯_w ρ_{Q-|w|})(y) ≤ ρ_Q(y)`, where `y` is read in `G_{Q-|w|+|w|} = G_Q`. -/
@[collatz_pos_dens "lem_prefix_family_le"]
theorem sum_transfer_refDensity_le {V : Finset Word} (hV : IsPrefixFree (V : Set Word))
    {h Q : ℕ} (hlen : ∀ w ∈ V, w.length ≤ h) (hQ : h ≤ Q) (y : ResidueGroup Q) :
    ∑ w ∈ V, transfer w (refDensity (Q - w.length))
        (y.cast : ResidueGroup (Q - w.length + w.length)) ≤ refDensity Q y := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hQ
  have key (w : Word) (hw : w.length ≤ h) :
      ENNReal.ofReal (transfer w (refDensity (t + h - w.length))
        (y.cast : ResidueGroup (t + h - w.length + w.length))) =
      ∑' v : {v : Word | v.length = h - w.length}, ENNReal.ofReal (transfer (w ++ v.1)
        (refDensity t) (y.cast : ResidueGroup (t + (w ++ v.1).length))) := by
    have hs : t + h - w.length = t + (h - w.length) := by omega
    have gen : ∀ s (hs : s = t + (h - w.length)),
        ENNReal.ofReal (transfer w (refDensity s)
          (y.cast : ResidueGroup (s + w.length))) =
        ∑' v : {v : Word | v.length = h - w.length}, ENNReal.ofReal (transfer (w ++ v.1)
          (refDensity t) (y.cast : ResidueGroup (t + (w ++ v.1).length))) := by
      rintro s rfl
      rw [← prefixFamilyLe_cast_eq_zmodCast (show t + h = t + (h - w.length) + w.length by omega),
        ofReal_transfer_refDensity_add_eq_tsum]
      refine tsum_congr fun v => ?_
      have hv : v.1.length = h - w.length := v.2
      rw [cast_cast, prefixFamilyLe_cast_eq_zmodCast]
      rw [List.length_append, hv]
      omega
    exact gen _ hs
  set G : {u : Word | u.length = h} → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (transfer u.1 (refDensity t) (y.cast : ResidueGroup (t + u.1.length)))
    with hG
  rw [← ENNReal.ofReal_le_ofReal_iff (refDensity_nonneg _ _),
    ENNReal.ofReal_sum_of_nonneg fun w _ => transfer_nonneg _ (fun z => refDensity_nonneg _ z) _,
    Finset.sum_congr rfl fun w hw => key w (hlen w hw), ofReal_refDensity_add_eq_tsum_transfer,
    ← Finset.tsum_subtype V]
  calc _ = ∑' p : Σ w : V, {v : Word | v.length = h - (w : Word).length},
          G (prefixFamilyLeConcat V h hlen p) :=
        (ENNReal.tsum_sigma' fun p => G (prefixFamilyLeConcat V h hlen p)).symm
    _ ≤ ∑' u, G u :=
        ENNReal.tsum_comp_le_tsum_of_injective (prefixFamilyLeConcat_injective hV h hlen) G
    _ = _ := by
      refine tsum_congr fun u => ?_
      rw [hG, prefixFamilyLe_cast_eq_zmodCast]
      exact congrArg _ u.2.symm

end CollatzPosDens
