/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.RefLaw
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxOscPerturb
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxSubmassLe
public import CollatzPosDens.Mixing.MxSubmassTotal
public import CollatzPosDens.Mixing.MxSubmassUnion
public import CollatzPosDens.Mixing.MxShRetained
public import CollatzPosDens.Mixing.MxShRetainedOsc
public import CollatzPosDens.Mixing.MxShComplement
public import CollatzPosDens.Mixing.MxShLocal

/-!
# The fixed-clock shell sum

Let `ι : FIndex` and let `n ≥ 2^80` and `m ≤ n` with `25 n ≤ 27 m`. Then the reference law
`refLaw n` satisfies
$$\mathrm{Osc}_{m,n}(\mu_n) \le Q_ι(n),$$
where `Q_ι(x) = 18 B_F(ι) x^{-a(ι)} log x + 15 x^{-2}` is `mxShLocal ι x`, with
`B_F(ι) = fourierPrefactor ι` and `a(ι) = amix ι`.

Write `R = shRetained n` for the retained words of length `n`. The reference law `μ_n` is the
submass of all words of length `n`, hence the sum of the submasses of `R` and of its complement
`ℤ_{≥1}^n \ R`. The perturbation bound for the oscillation, together with the total of the
submasses, gives
$$\mathrm{Osc}_{m,n}(\mu_n) \le \mathrm{Osc}_{m,n}(\mathrm{Sub}^n_{\mathcal R})
  + 2\,\mathbf p(\mathbb Z_{\ge1}^n \setminus \mathcal R)
  \le 18 B_F(ι) n^{-a(ι)} \log n + 14 n^{-2} + 8 n^{-16}.$$
Finally `8 n^{-16} ≤ n^{-2}`, as `n^{14} ≥ 8`.

## Main results

* `CollatzPosDens.oscillation_refLaw_le_mxShLocal`: for `2^80 ≤ n`, `m ≤ n` and `25 n ≤ 27 m`,
  the oscillation of `refLaw n` is at most `mxShLocal ι n`.

## Implementation notes

The statement assumes only `2^80 ≤ n`, not `2^80 ≤ m`. The `[0, ∞]`-valued law `refLaw n` enters
the real-valued oscillation through `ENNReal.toReal`; all its values are at most one.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

open Finset

/-- The mass outside the retained words controls the distance between `μ_n` and the submass
of the retained words: `∑_y |μ_n(y) - Sub^n_R(y)| ≤ 7 n^{-2} + 4 n^{-16}`. -/
private theorem sum_abs_refLaw_sub_subMass_shRetained_le {n : ℕ} (hn : mxGateLevel ≤ n) :
    ∑ y, |(refLaw n y).toReal - (subMass n (shRetained n) y).toReal| ≤
      7 * (n : ℝ) ^ (-2 : ℝ) + 4 * (n : ℝ) ^ (-16 : ℝ) := by
  set C : Set Word := {w : Word | w.length = n ∧ w ∉ shRetained n} with hC
  have hRlen : shRetained n ⊆ {w : Word | w.length = n} := fun _ hw => length_of_mem_shRetained hw
  have hClen : C ⊆ {w : Word | w.length = n} := fun _ hw => hw.1
  have hdisj : Disjoint (shRetained n) C := Set.disjoint_left.2 fun _ hR hC => hC.2 hR
  have hunion : {w : Word | w.length = n} = shRetained n ∪ C := by
    ext w
    simp only [Set.mem_union, Set.mem_ofPred_eq, hC]
    constructor
    · intro hw
      by_cases hR : w ∈ shRetained n
      · exact Or.inl hR
      · exact Or.inr ⟨hw, hR⟩
    · rintro (hR | hw)
      · exact length_of_mem_shRetained hR
      · exact hw.1
  have hy : ∀ y, |(refLaw n y).toReal - (subMass n (shRetained n) y).toReal| =
      (subMass n C y).toReal := by
    intro y
    rw [← subMass_length_eq_refLaw, hunion, subMass_union n hdisj,
      ENNReal.toReal_add (subMass_ne_top_of_subset_length n hRlen y)
        (subMass_ne_top_of_subset_length n hClen y), add_sub_cancel_left,
      abs_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [hy]
  rw [← ENNReal.toReal_sum fun y _ => subMass_ne_top_of_subset_length n hClen y, sum_subMass]
  have hb := geomMass_setOf_length_and_notMem_shRetained_le hn
  rw [← hC] at hb
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans
    (ENNReal.toReal_ofReal (by positivity)).le

/-- **The fixed-clock shell sum.** Let `ι` be a Fourier index, `n ≥ n₀` and `m ≤ n` with
`25 n ≤ 27 m`. Then `Osc_{m,n}(μ_n) ≤ Q_ι(n)`. -/
@[collatz_pos_dens "lem_mx_sh_joint"]
theorem oscillation_refLaw_le_mxShLocal (ι : FIndex) {n m : ℕ} (hn : mxGateLevel ≤ n)
    (hmn : m ≤ n) (h25 : 25 * n ≤ 27 * m) :
    oscillation hmn (fun y => (refLaw n y).toReal) ≤ mxShLocal ι n := by
  have hn80 : 2 ^ 80 ≤ n := by rwa [mxGateLevel_def] at hn
  have hosc := oscillation_subMass_shRetained_le ι hn hmn h25
  have hdef := sum_abs_refLaw_sub_subMass_shRetained_le hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast (show 8 ≤ n by omega)
  have h16 : 8 * (n : ℝ) ^ (-16 : ℝ) ≤ (n : ℝ) ^ (-2 : ℝ) := by
    have hsplit : (n : ℝ) ^ (-16 : ℝ) = (n : ℝ) ^ (-2 : ℝ) * ((n : ℝ) ^ (14 : ℕ))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_neg hnpos.le, ← Real.rpow_add hnpos]
      norm_num
    have h14 : (8 : ℝ) ≤ (n : ℝ) ^ (14 : ℕ) :=
      hn8.trans (le_self_pow₀ (by linarith) (by norm_num))
    have hinv : ((n : ℝ) ^ (14 : ℕ))⁻¹ ≤ 1 / 8 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) h14
    have h2 : 0 ≤ (n : ℝ) ^ (-2 : ℝ) := by positivity
    rw [hsplit]
    nlinarith
  calc oscillation hmn (fun y => (refLaw n y).toReal)
      ≤ oscillation hmn (fun y => (subMass n (shRetained n) y).toReal) +
          2 * ∑ y, |(refLaw n y).toReal - (subMass n (shRetained n) y).toReal| :=
        oscillation_le_add_two_mul_sum_abs_sub hmn _ _
    _ ≤ 18 * fourierPrefactor ι * (n : ℝ) ^ (-(amix ι : ℝ)) * Real.log n +
          2 * (7 * (n : ℝ) ^ (-2 : ℝ) + 4 * (n : ℝ) ^ (-16 : ℝ)) := by gcongr
    _ ≤ 18 * fourierPrefactor ι * (n : ℝ) ^ (-(amix ι : ℝ)) * Real.log n +
          15 * (n : ℝ) ^ (-2 : ℝ) := by linarith
    _ = mxShLocal ι n := by rw [mxShLocal_def]

end CollatzPosDens
