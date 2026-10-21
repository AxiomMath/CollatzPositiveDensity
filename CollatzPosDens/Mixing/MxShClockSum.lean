/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShFreshWord

/-!
# The binary-clock law

Let `N, n, d ∈ ℕ` with `d < n`. Write `A(w)` for `CollatzPosDens.Word.valSum w`, `Ex_N(w)` for
`CollatzPosDens.Word.exposedPattern N w`, `Fr_N(w)` for `CollatzPosDens.Word.fresh N w` and
`Pt(u)` for `CollatzPosDens.Word.partialSums u`. Under the geometric weight `2^{-A(w)}` on words
of length `n`, the exposed pattern `Ex_N(w)` and the fresh word `Fr_N(w)` of the words with
`|Ex_N(w)| = d` are independent: the pattern is uniform on the `d`-element subsets of
`{1, …, N}`, each of mass `2^{-N}`, and the fresh word carries the geometric weight on words of
length `n - d`. Precisely, for every `F` with values in `[0, ∞]`,
$$\sum_{\substack{w \in \mathbb{Z}_{\ge 1}^n \\ |\mathrm{Ex}_N(w)| = d}} 2^{-A(w)}\,
  F(\mathrm{Ex}_N(w), \mathrm{Fr}_N(w))
  = 2^{-N} \sum_{\substack{\beta \subseteq \{1,\dots,N\} \\ |\beta| = d}}\
    \sum_{v \in \mathbb{Z}_{\ge 1}^{n-d}} 2^{-A(v)}\, F(\beta, v).$$
The map `w ↦ (Ex_N(w), Fr_N(w))` is a bijection between the two index sets: writing
`w = u a r` with `A(u) ≤ N < A(u) + a`, one has `Ex_N(w) = Pt(u)` and
`Fr_N(w) = (A(u) + a - N, r)`, and `w` is recovered from `(β, (b, r))` as `u a r` with
`Pt(u) = β` and `a = b + N - A(u)`. Moreover `A(w) = N + A(Fr_N(w))`.

## Main definitions

* `CollatzPosDens.Word.exposedPatternFresh`: the map `w ↦ (Ex_N(w), Fr_N(w))`.

## Main results

* `CollatzPosDens.Word.bijective_exposedPattern_fresh`: the bijection `w ↦ (Ex_N(w), Fr_N(w))`.
* `CollatzPosDens.Word.tsum_exposedPattern_fresh`: the binary-clock law.

## Implementation notes

The function `F` is taken on all pairs `(β, v)` of a finite set of naturals and a word; only its
values at `β ⊆ {1, …, N}` with `|β| = d` and `|v| = n - d` enter. The geometric weight `2^{-A(w)}`
is written `2⁻¹ ^ A(w)` in `ℝ≥0∞`, and the sums over words are unconditional sums over subtypes.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace Word

open Finset
open scoped ENNReal

/-- The map `w ↦ (Ex_N(w), Fr_N(w))` from words of length `n` with `|Ex_N(w)| = d < n` to pairs
of a `d`-element subset of `{1, …, N}` and a word of length `n - d`. -/
def exposedPatternFresh (N n d : ℕ) (hdn : d < n)
    (w : {w : Word // w.length = n ∧ #(exposedPattern N w) = d}) :
    (Icc 1 N).powersetCard d × {v : Word // v.length = n - d} :=
  (⟨exposedPattern N w.1, mem_powersetCard.2 ⟨exposedPattern_subset_Icc N w.1, w.2.2⟩⟩,
    ⟨fresh N w.1, by rw [length_fresh (by omega), w.2.1, w.2.2]⟩)

/-- The map `w ↦ (Ex_N(w), Fr_N(w))` is a bijection from the words of length `n` with
`|Ex_N(w)| = d < n` onto the pairs of a `d`-element subset of `{1, …, N}` and a word of length
`n - d`. -/
theorem bijective_exposedPattern_fresh (N n d : ℕ) (hdn : d < n) :
    Function.Bijective (exposedPatternFresh N n d hdn) := by
  constructor
  · rintro ⟨w, hwn, hwd⟩ ⟨w', hwn', hwd'⟩ h
    simp only [exposedPatternFresh, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨u, a, r, rfl, hu, ha⟩ :=
      exists_eq_append_cons_of_card_exposedPattern_lt (N := N) (w := w) (by omega)
    obtain ⟨u', a', r', rfl, hu', ha'⟩ :=
      exists_eq_append_cons_of_card_exposedPattern_lt (N := N) (w := w') (by omega)
    rw [exposedPattern_append_cons r hu ha, exposedPattern_append_cons r' hu' ha'] at h
    obtain rfl := partialSums_injective h.1
    rw [fresh_append_cons r hu ha, fresh_append_cons r' hu' ha', List.cons.injEq] at h
    obtain ⟨h₁, rfl⟩ := h.2
    have h₂ := congrArg ((↑) : ℕ+ → ℕ) h₁
    rw [coe_toPNat'_valSum_add_sub ha, coe_toPNat'_valSum_add_sub ha'] at h₂
    obtain rfl : a = a' := PNat.coe_injective (by omega)
    rfl
  · rintro ⟨⟨β, hβ⟩, ⟨_ | ⟨b, r⟩, hv⟩⟩
    · simp at hv
      omega
    obtain ⟨hβN, hβd⟩ := mem_powersetCard.1 hβ
    obtain ⟨u, rfl⟩ := exists_partialSums_eq β fun h0 => by simpa using hβN h0
    have hu : valSum u ≤ N := by
      rcases eq_or_ne u [] with rfl | hne
      · exact Nat.zero_le _
      · exact (mem_Icc.1 (hβN (valSum_mem_partialSums hne))).2
    set a : ℕ+ := ⟨(b : ℕ) + (N - valSum u), by positivity⟩ with ha_def
    have ha : N < valSum u + a := by
      simp only [ha_def, PNat.mk_coe]
      have := b.pos
      omega
    rw [card_partialSums] at hβd
    refine ⟨⟨u ++ a :: r, ?_, ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_cons] at hv ⊢
      omega
    · rw [card_exposedPattern_append_cons r hu ha, hβd]
    · simp only [exposedPatternFresh, Prod.mk.injEq, Subtype.mk.injEq]
      refine ⟨exposedPattern_append_cons r hu ha, ?_⟩
      rw [fresh_append_cons r hu ha, List.cons.injEq]
      refine ⟨PNat.coe_injective ?_, rfl⟩
      rw [coe_toPNat'_valSum_add_sub ha]
      simp only [ha_def, PNat.mk_coe]
      omega

/-- **The binary-clock law.** For `N, n, d ∈ ℕ` with `d < n` and every `F` with values in
`[0, ∞]`,
`∑_{w ∈ ℤ_{≥1}^n, |Ex_N(w)| = d} 2^{-A(w)} F(Ex_N(w), Fr_N(w))
  = 2^{-N} ∑_{β ⊆ {1,…,N}, |β| = d} ∑_{v ∈ ℤ_{≥1}^{n-d}} 2^{-A(v)} F(β, v)`. -/
@[collatz_pos_dens "lem_mx_sh_clock_sum"]
theorem tsum_exposedPattern_fresh (N n d : ℕ) (hdn : d < n) (F : Finset ℕ → Word → ℝ≥0∞) :
    ∑' w : {w : Word // w.length = n ∧ #(exposedPattern N w) = d},
        (2⁻¹ : ℝ≥0∞) ^ valSum w.1 * F (exposedPattern N w.1) (fresh N w.1) =
      (2⁻¹ : ℝ≥0∞) ^ N * ∑ β ∈ (Icc 1 N).powersetCard d,
        ∑' v : {v : Word // v.length = n - d}, (2⁻¹ : ℝ≥0∞) ^ valSum v.1 * F β v.1 := by
  set g : (Icc 1 N).powersetCard d × {v : Word // v.length = n - d} → ℝ≥0∞ :=
    fun p => (2⁻¹ : ℝ≥0∞) ^ N * ((2⁻¹ : ℝ≥0∞) ^ valSum p.2.1 * F p.1.1 p.2.1) with hg
  have hw : ∀ w : {w : Word // w.length = n ∧ #(exposedPattern N w) = d},
      (2⁻¹ : ℝ≥0∞) ^ valSum w.1 * F (exposedPattern N w.1) (fresh N w.1) =
        g (exposedPatternFresh N n d hdn w) := by
    rintro ⟨w, hwn, hwd⟩
    simp only [hg, exposedPatternFresh]
    rw [← valSum_fresh (N := N) (w := w) (by omega), pow_add, ← mul_assoc, mul_comm (_ ^ N)]
  simp_rw [hw]
  refine ((Equiv.ofBijective _ (bijective_exposedPattern_fresh N n d hdn)).tsum_eq g).trans ?_
  rw [ENNReal.tsum_prod', hg]
  simp_rw [ENNReal.tsum_mul_left]
  congr 1
  exact Finset.tsum_subtype ((Icc 1 N).powersetCard d) fun β =>
    ∑' v : {v : Word // v.length = n - d}, (2⁻¹ : ℝ≥0∞) ^ valSum v.1 * F β v.1

end Word

end CollatzPosDens
