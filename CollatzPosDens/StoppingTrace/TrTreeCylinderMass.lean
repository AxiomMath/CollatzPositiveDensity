/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.CharSum.ChRawLaw
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.StoppingTrace.TrConcat
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPathGrowthJ
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass

/-!
# Mass of entry lists with a given raw prefix

Fix a level `n`, a residue `ξ`, a colour scale `ε` and a point `v`. For `k ∈ ℕ` and
`λ ∈ ℤ^k`, let `E_λ` be the set of entry lists `u ∈ 𝓔(v)` whose raw word has length at least
`k` and begins with `λ`. Then
`∑_{u ∈ E_λ} bw^⊗(u) ≤ ∏_{i=1}^k ϖ(λᵢ)`.

Put `J = ⌊n/2⌋`. The endpoint of an entry list `u` is black, so `j(v) + |u| ≤ J`; hence all
entry lists have length at most some `M ≥ k`. The entry lists form a prefix-free family, so the
cylinders `C(u) = {β ∈ 𝔅^M : β_{[1,|u|]} = u}`, `u ∈ E_λ`, are pairwise disjoint, and `C(u)` has
weight `bw^⊗(u)`. Every `β ∈ C(u)` has raw word beginning with that of `u`, hence
`raw_k(β) = λ`. So the sum is at most the weight of the lists `β ∈ 𝔅^M` with `raw_k(β) = λ`,
which is `∏ᵢ ϖ(λᵢ)` by the law of the raw prefix.

## Main results

* `CollatzPosDens.chRaw_eq_iff_prefix`: `raw_k(β) = λ` iff the raw word of `β` begins with `λ`
  (for `λ` of length `k`).
* `CollatzPosDens.tsum_trListWeight_trEntryWords_chRaw_le`: the cylinder mass bound.

## Implementation notes

The condition "the raw word of `u` has length at least `k` and begins with `λ`" is stated as
`raw_k(u) = λ`, i.e. `chRaw k u = List.ofFn λ`; `chRaw_eq_iff_prefix` shows the two are equivalent.
The word `λ ∈ ℤ^k` is a function `Fin k → ℤ`, as in
`CollatzPosDens.hasSum_prod_chBlockWeight_chRaw_eq`. The sum is the unconditional sum in `[0, ∞]`
of the nonnegative real weights embedded through `ENNReal.ofReal`, as in `CollatzPosDens.trKernel`.
The point `v` need not be black; the argument uses only that the endpoints of entry lists are
black, which bounds their lengths by `⌊n/2⌋ - j(v)`, so the bound holds for every `n`, `ξ`, `ε` and
every point `v ∈ ℤ × ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- For a word `w`, `raw_{|w|}(β) = w` iff the raw word of `β` begins with `w`. -/
theorem chRaw_eq_iff_prefix {α : Type*} (w : List α) (β : List (List α × α)) :
    chRaw w.length β = w ↔ w <+: β.flatMap fun b => b.1 ++ [b.2] := by
  rw [chRaw_def]
  exact ⟨fun h ↦ h ▸ List.take_prefix _ _, fun h ↦ (List.prefix_iff_eq_take.mp h).symm⟩

/-- If `u` is a prefix of `β` and `raw_k(u)` has length `k`, then `raw_k(β) = raw_k(u)`. -/
theorem chRaw_eq_of_prefix {α : Type*} {k : ℕ} {u β : List (List α × α)} (huβ : u <+: β)
    (hk : (chRaw k u).length = k) : chRaw k β = chRaw k u := by
  obtain ⟨f, rfl⟩ := huβ
  rw [chRaw_def, chRaw_def, List.flatMap_append, List.take_append_of_le_length]
  rw [chRaw_def, List.length_take] at hk
  omega

/-- The length of an entry list from `v` is at most `⌊n/2⌋ - j(v)`. -/
theorem length_le_of_mem_trEntryWords {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {v : ℤ × ℤ}
    {u : List (List ℤ × ℤ)} (hu : u ∈ trEntryWords n ξ ε v) :
    u.length ≤ (((n / 2 : ℕ) : ℤ) - bkJ v).toNat := by
  have hg := trPath_bkJ_sub_bkJ_ge v u (Nat.zero_le u.length)
  simp only [min_self, Nat.zero_min, trPath_zero, CharP.cast_eq_zero, sub_zero] at hg
  have := (trEntryWords_bkBlack hu).bkJ_le
  omega

/-- The weight of the block lists `β ∈ 𝔅^N` with `raw_k(β) = λ`, for `k ≤ N`, is
`∏ᵢ ϖ(λᵢ)`. -/
theorem tsum_trListWeight_chRaw_eq {k N : ℕ} (hkN : k ≤ N) (lam : Fin k → ℤ) :
    ∑' β : {β : List (List ℤ × ℤ) //
        β.length = N ∧ ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}},
      ENNReal.ofReal (trListWeight β.1) * (if chRaw k β.1 = List.ofFn lam then 1 else 0) =
      ENNReal.ofReal (∏ i, varpi (lam i)) := by
  have h := hasSum_prod_chBlockWeight_chRaw_eq hkN lam
  have h0 : ∀ x : Fin N → {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)},
      0 ≤ (∏ i, chBlockWeight (x i)) *
        if chRaw k (List.ofFn fun i ↦ (x i).1) = List.ofFn lam then 1 else 0 := fun x ↦
    mul_nonneg (prod_chBlockWeight_nonneg x) (by split_ifs <;> norm_num)
  rw [← (blockListEquivFin N).symm.tsum_eq, ← h.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg h0 h.summable]
  refine tsum_congr fun x ↦ ?_
  simp only [blockListEquivFin, Equiv.coe_fn_symm_mk, trListWeight_ofFn]
  rw [ENNReal.ofReal_mul (prod_chBlockWeight_nonneg x)]
  by_cases hc : chRaw k (List.ofFn fun i ↦ (x i).1) = List.ofFn lam <;> simp [hc]

/-- **Mass of entry lists with a given raw prefix.** For `k ∈ ℕ` and `λ ∈ ℤ^k`, the entry lists
`u ∈ 𝓔(v)` whose raw word has length at least `k` and begins with `λ` (that is,
`raw_k(u) = λ`) have total weight `∑ bw^⊗(u) ≤ ∏_{i=1}^k ϖ(λᵢ)`. -/
@[collatz_pos_dens "lem_tr_tree_cylinder_mass"]
theorem tsum_trListWeight_trEntryWords_chRaw_le (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    (v : ℤ × ℤ) (k : ℕ) (lam : Fin k → ℤ) :
    ∑' u : {u : List (List ℤ × ℤ) // u ∈ trEntryWords n ξ ε v ∧ chRaw k u = List.ofFn lam},
      ENNReal.ofReal (trListWeight u.1) ≤ ENNReal.ofReal (∏ i, varpi (lam i)) := by
  set M := max (((n / 2 : ℕ) : ℤ) - bkJ v).toNat k
  set E := {u : List (List ℤ × ℤ) // u ∈ trEntryWords n ξ ε v ∧ chRaw k u = List.ofFn lam}
  set B := {β : List (List ℤ × ℤ) //
    β.length = M ∧ ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}}
  have hlen : ∀ u : E, u.1.length ≤ M := fun u ↦
    (length_le_of_mem_trEntryWords u.2.1).trans (le_max_left _ _)
  calc ∑' u : E, ENNReal.ofReal (trListWeight u.1)
      = ∑' u : E, ∑' β : B, ENNReal.ofReal (trListWeight β.1) *
          (if β.1.take u.1.length = u.1 then 1 else 0) :=
        tsum_congr fun u ↦ (tsum_trListWeight_le_one_of_prefixFree_cylinder u.1
          (fun x hx ↦ trEntryWords_closing_mem u.2.1 hx) (hlen u)).symm
    _ = ∑' β : B, ENNReal.ofReal (trListWeight β.1) *
          ∑' u : E, (if β.1.take u.1.length = u.1 then 1 else 0) := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun β ↦ ENNReal.tsum_mul_left
    _ ≤ ∑' β : B, ENNReal.ofReal (trListWeight β.1) *
          (if chRaw k β.1 = List.ofFn lam then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun β ↦ mul_le_mul_right ?_ _
        by_cases hex : ∃ w : E, β.1.take w.1.length = w.1
        · obtain ⟨w, hw⟩ := hex
          have hwp : w.1 <+: β.1 := hw ▸ List.take_prefix _ _
          have hraw : chRaw k β.1 = List.ofFn lam := by
            rw [chRaw_eq_of_prefix hwp (by rw [w.2.2, List.length_ofFn]), w.2.2]
          simp only [hraw, ↓reduceIte]
          rw [tsum_eq_single w]
          · simp [hw]
          · intro u hu
            refine ite_eq_right fun hu' ↦ (hu ?_).elim
            have hup : u.1 <+: β.1 := hu' ▸ List.take_prefix _ _
            rcases le_total u.1.length w.1.length with h | h
            · exact Subtype.ext (isPrefixFree_trEntryWords _ u.2.1 _ w.2.1
                (List.prefix_of_prefix_length_le hup hwp h))
            · exact Subtype.ext (isPrefixFree_trEntryWords _ w.2.1 _ u.2.1
                (List.prefix_of_prefix_length_le hwp hup h)).symm
        · push Not at hex
          simp [hex]
    _ = ENNReal.ofReal (∏ i, varpi (lam i)) :=
        tsum_trListWeight_chRaw_eq (le_max_right _ _) lam

end CollatzPosDens
