/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02DyadicReduction
public import CollatzPosDens.Mixing.MxOffsetInjective
public import CollatzPosDens.Mixing.MxShHeadMeasure
public import CollatzPosDens.Mixing.MxShPartialSumsBij
public import CollatzPosDens.Mixing.MxShPartialSumsOffset
public import CollatzPosDens.Mixing.MxShResidueCount

/-!
# Multiplicity of patterns in a narrow offset window

Let `n, N, d ∈ ℕ`, let `E` be a set of `d`-element subsets of `{1, …, N}`, and let `α, λ` be reals
with `λ ≥ 0` such that `α ≤ Of(β) < α + λ` for every `β ∈ E`. Then for every residue `y ∈ G_n`
$$\#\{\beta \in E : [\mathrm{Of}(\beta)]_n = y\} \le 2^N \lambda\, 3^{-n} + 1.$$

Indeed, `t_β = 2^N Of(β)` is a natural number, since every position of `β` is at most `N`. The map
`β ↦ t_β` is injective on `E`: two `d`-subsets with the same offset are the partial-sum sets of two
words of length `d` with the same offset, and the offset is injective on words of a fixed length.
The patterns with `[Of(β)]_n = y` have `t_β ≡ c (mod 3^n)` for a fixed integer `c` representing
`[2^N]_n y`, and `2^N α ≤ t_β ≤ 2^N α + 2^N λ`; an interval of length `2^N λ` contains at most
`2^N λ 3^{-n} + 1` integers of one residue class modulo `3^n`.

## Main results

* `CollatzPosDens.exists_setOffset_mul_two_pow_eq_natCast`: `2^N Of(β)` is a natural number when
  every element of `β` is at most `N`.
* `CollatzPosDens.eq_of_setOffset_eq_of_card_eq`: the offset is injective on `d`-element sets of
  positive integers.
* `CollatzPosDens.card_filter_dyadicRed_setOffset_le`: the multiplicity bound above.

## Implementation notes

The set `E` is a `Finset` of `Finset ℕ`; a set of subsets of `{1, …, N}` is finite, so this loses
no generality.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset Word

/-- `2^N Of(β)` is a natural number when every element of `β` is at most `N`. -/
theorem exists_setOffset_mul_two_pow_eq_natCast {N : ℕ} {β : Finset ℕ} (hβ : ∀ s ∈ β, s ≤ N) :
    ∃ t : ℕ, setOffset β * 2 ^ N = t := by
  refine ⟨∑ s ∈ β, 3 ^ #(β.filter (· < s)) * 2 ^ (N - s), ?_⟩
  rw [setOffset, Finset.sum_mul]
  push_cast
  refine Finset.sum_congr rfl fun s hs => ?_
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hβ s hs)
  rw [hm, Nat.add_sub_cancel_left, pow_add]
  field_simp

/-- The subset offset is injective on sets of positive integers of a common cardinality. -/
theorem eq_of_setOffset_eq_of_card_eq {S S' : Finset ℕ} (hS : 0 ∉ S) (hS' : 0 ∉ S')
    (hcard : #S = #S') (h : setOffset S = setOffset S') : S = S' := by
  obtain ⟨v, rfl⟩ := exists_partialSums_eq S hS
  obtain ⟨v', rfl⟩ := exists_partialSums_eq S' hS'
  rw [card_partialSums, card_partialSums] at hcard
  rw [← off_eq_setOffset_partialSums, ← off_eq_setOffset_partialSums] at h
  rw [off_injective_of_length_eq hcard h]

/-- **Multiplicity of patterns in a narrow offset window.** Let `E` be a set of `d`-element subsets
of `{1, …, N}` and `α, λ` reals with `λ ≥ 0` and `α ≤ Of(β) < α + λ` for every `β ∈ E`. Then for
every `y ∈ G_n`, `#{β ∈ E : [Of(β)]_n = y} ≤ 2^N λ 3^{-n} + 1`. -/
@[collatz_pos_dens "lem_mx_sh_mult_sup"]
theorem card_filter_dyadicRed_setOffset_le (n N d : ℕ) {E : Finset (Finset ℕ)}
    (hE : ∀ β ∈ E, β ⊆ Icc 1 N ∧ #β = d) {α L : ℝ} (hL : 0 ≤ L)
    (hoff : ∀ β ∈ E, α ≤ (setOffset β : ℝ) ∧ (setOffset β : ℝ) < α + L) (y : ResidueGroup n) :
    (#{β ∈ E | dyadicRed n ⟨setOffset β, setOffset_mem_dyadicRationals β⟩ = y} : ℝ) ≤
      2 ^ N * L * 3⁻¹ ^ n + 1 := by
  set F := {β ∈ E | dyadicRed n ⟨setOffset β, setOffset_mem_dyadicRationals β⟩ = y}
  -- integrality: `t_β = 2^N Of(β)`
  set t : Finset ℕ → ℤ := fun β => ⌊setOffset β * 2 ^ N⌋
  have ht : ∀ β ∈ E, ((t β : ℤ) : ℚ) = setOffset β * 2 ^ N := fun β hβ => by
    obtain ⟨m, hm⟩ := exists_setOffset_mul_two_pow_eq_natCast (N := N) (β := β)
      fun s hs => (mem_Icc.1 ((hE β hβ).1 hs)).2
    simp only [t, hm]
    rw [show ((m : ℚ)) = ((m : ℤ) : ℚ) by simp, Int.floor_intCast]
  -- injectivity
  have hzero : ∀ β ∈ E, 0 ∉ β := fun β hβ h => by
    simpa using (hE β hβ).1 h
  have hinj : Set.InjOn t (F : Set (Finset ℕ)) := fun β hβ β' hβ' h => by
    have hβE := (mem_filter.1 hβ).1
    have hβE' := (mem_filter.1 hβ').1
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    simp only [ht β hβE, ht β' hβE'] at hq
    exact eq_of_setOffset_eq_of_card_eq (hzero β hβE) (hzero β' hβE')
      ((hE β hβE).2.trans (hE β' hβE').2.symm) (mul_right_cancel₀ (by positivity) hq)
  -- the residue condition
  set c : ℤ := ((y * 2 ^ N : ResidueGroup n).val : ℤ)
  have hres : ∀ β ∈ F, t β ≡ c [ZMOD 3 ^ n] := fun β hβ => by
    obtain ⟨hβE, hy⟩ := mem_filter.1 hβ
    have hsub : (⟨((t β : ℤ) : ℚ), by simp⟩ : dyadicRationals) =
        ⟨setOffset β, setOffset_mem_dyadicRationals β⟩ * 2 ^ N :=
      Subtype.ext (by
        have h2 : ((2 : dyadicRationals) : ℚ) = 2 := rfl
        simp [ht β hβE, h2])
    have h1 := congrArg (dyadicRed n) hsub
    rw [dyadicRed_intCast, map_mul, map_pow, map_ofNat, hy] at h1
    have h3 : ((c : ℤ) : ResidueGroup n) = ((t β : ℤ) : ResidueGroup n) := by
      rw [h1]; simp [c]
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub c (t β) (3 ^ n)).1 h3
    push_cast at this
    exact (Int.modEq_iff_dvd.2 this).symm
  -- the target set of integers
  set T : Set ℤ :=
    {u : ℤ | 2 ^ N * α ≤ u ∧ (u : ℝ) ≤ 2 ^ N * α + 2 ^ N * L ∧ u ≡ c [ZMOD 3 ^ n]}
  have hmaps : ∀ β ∈ (F : Set (Finset ℕ)), t β ∈ T := fun β hβ => by
    have hβE := (mem_filter.1 hβ).1
    have hR : ((t β : ℤ) : ℝ) = (setOffset β : ℝ) * 2 ^ N := by exact_mod_cast ht β hβE
    obtain ⟨h1, h2⟩ := hoff β hβE
    have h4 : (0 : ℝ) < 2 ^ N := by positivity
    refine ⟨by rw [hR]; nlinarith, by rw [hR]; nlinarith, hres β hβ⟩
  have hfin : T.Finite := finite_setOf_modEq_of_mem_Icc _ _ _ _
  have hcard := Set.ncard_le_ncard_of_injOn t hmaps hinj hfin
  rw [Set.ncard_coe_finset] at hcard
  have hbound := ncard_setOf_modEq_pow_three_le n c (α := 2 ^ N * α)
    (L := 2 ^ N * L) (by positivity)
  calc (#F : ℝ) ≤ T.ncard := by exact_mod_cast hcard
    _ ≤ 2 ^ N * L * 3⁻¹ ^ n + 1 := hbound

end CollatzPosDens
