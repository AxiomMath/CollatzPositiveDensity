/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxOffsetTail
public import CollatzPosDens.Mixing.MxShClockOffset
public import CollatzPosDens.Mixing.MxShProbeTail
public import CollatzPosDens.Mixing.MxShRetained
public import CollatzPosDens.Mixing.MxShWindowHigh
public import CollatzPosDens.Mixing.MxShWindowLow

/-!
# Mass outside the retained words

For every integer `n ≥ n₀ = 2^80`, the words of length `n` outside the set `R^{sh}_n` of retained
words of the shell cut have geometric mass
$$\mathbf p\bigl(\mathbb Z_{\ge1}^n \setminus \mathcal R^{\mathrm{sh}}_n\bigr)
  \le 7 n^{-2} + 4 n^{-16}.$$

Write `H = H^{sh}_n`, `N = H - 1`, `h = h^{sh}_n`, `J = J^{sh}_n`, `k^± = k^{sh,±}_n` and
`S_i = A(w_{≤ i})`. By `one_le_shKLo`, `mul_shKHi_lt`, `shKLo_eq` and `shKHi_eq`, one has
`1 ≤ k^- < k^+ ≤ n`, `H - 2k^- ≥ 2h` and `2k^+ - H ≥ 2h`. A word of length `n` lies in `R^{sh}_n`
unless one of the following happens: `|S_{k^-} - 2k^-| ≥ 2h`, `|S_{k^+} - 2k^+| ≥ 2h`, or
`off(w) ≥ 2^J`. Indeed, otherwise `S_{k^-} ≤ N < S_{k^+}`, so the exposed pattern `β = Ex_N(w)`
has `D = |β|` elements with `k^- ≤ D ≤ k^+ - 1 ≤ n - 1`; by
`Word.off_eq_setOffset_exposedPattern_add`, `Of(β) ≤ off(w) < 2^J`, so `Of(β)` lies in a shell
`I^{sh}_j` with `j ≤ J`, and `w ∈ Sl^{sh}_n(D, j) ⊆ R^{sh}_n`.

The two deviation events have mass at most `2 n^{-16}` each by
`geomMass_abs_valSum_take_sub_ge_two_mul_shWidth_le`, and the offset event at most
`7 / (2^J + 2) ≤ 7 n^{-2}` by `geomMass_offsetTail_le`, since `2^J ≥ n^2`.

## Main results

* `CollatzPosDens.geomMass_setOf_length_and_notMem_shRetained_le`: the bound above.

## Implementation notes

The complement `ℤ_{≥1}^n \ R^{sh}_n` is the set of words `w` with `w.length = n` and
`w ∉ shRetained n`. The bound is the real number `7 n^{-2} + 4 n^{-16}`, with real powers,
embedded in `ℝ≥0∞` by `ENNReal.ofReal`.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- `n^2 ≤ 2^{J^{sh}_n}` for `n ≥ 1`. -/
private lemma sq_le_two_pow_shJ {n : ℕ} (hn : 1 ≤ n) : (n : ℝ) ^ 2 ≤ 2 ^ shJ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ := le_shJ n
  calc (n : ℝ) ^ 2 = (2 : ℝ) ^ (2 * Real.logb 2 n) := by
        rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0]
        norm_cast
    _ ≤ (2 : ℝ) ^ (shJ n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hJ
    _ = 2 ^ shJ n := Real.rpow_natCast _ _

/-- **Mass outside the retained words.** For every integer `n ≥ n₀ = 2^80`,
`𝐩(ℤ_{≥1}^n \ R^{sh}_n) ≤ 7 n^{-2} + 4 n^{-16}`. -/
@[collatz_pos_dens "lem_mx_sh_complement"]
theorem geomMass_setOf_length_and_notMem_shRetained_le {n : ℕ} (hn : mxGateLevel ≤ n) :
    geomMass {w : Word | w.length = n ∧ w ∉ shRetained n} ≤
      ENNReal.ofReal (7 * (n : ℝ) ^ (-2 : ℝ) + 4 * (n : ℝ) ^ (-16 : ℝ)) := by
  have hlo := one_le_shKLo hn
  have hhi := mul_shKHi_lt hn
  rw [mxGateLevel_def] at hn
  set H := shHeight n with hH
  set h := shWidth n with hh
  set J := shJ n with hJ
  set kl := (shKLo n).toNat with hkl
  set kh := (shKHi n).toNat with hkh
  have hn' : 1208925819614629174706176 ≤ n := by norm_num at hn; exact hn
  have hkleq := shKLo_eq n
  have hkheq := shKHi_eq n
  rw [← hH, ← hh] at hkleq hkheq
  have hkl1 : 1 ≤ kl := by omega
  have hkhle : kh ≤ n := by omega
  have hklH : 2 * kl + 2 * h ≤ H := by omega
  have hkhH : H + 2 * h ≤ 2 * kh := by omega
  have hkl_lo : shKLo n = (kl : ℤ) := by omega
  have hkh_hi : shKHi n = (kh : ℤ) := by omega
  set E₁ : Set Word := {w : Word | w.length = n ∧
    2 * (shWidth n : ℝ) ≤ |(Word.valSum (w.take kl) : ℝ) - 2 * kl|} with hE₁
  set E₂ : Set Word := {w : Word | w.length = n ∧
    2 * (shWidth n : ℝ) ≤ |(Word.valSum (w.take kh) : ℝ) - 2 * kh|} with hE₂
  set E₃ : Set Word := {w : Word | w.length = n ∧ (2 : ℝ) ^ J ≤ (off w : ℝ)} with hE₃
  have hsub : {w : Word | w.length = n ∧ w ∉ shRetained n} ⊆ E₁ ∪ E₂ ∪ E₃ := by
    rintro w ⟨hw, hnot⟩
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hc
    apply hnot
    set S : ℕ → ℕ := fun i => Word.valSum (w.take i) with hS
    have hS₁ : S kl < H := by
      have : ¬ (2 * (h : ℝ) ≤ |(S kl : ℝ) - 2 * kl|) := fun h' => h₁ ⟨hw, h'⟩
      rw [not_le, abs_lt] at this
      have : (S kl : ℝ) < H := by
        have : ((2 * kl + 2 * h : ℕ) : ℝ) ≤ H := by exact_mod_cast hklH
        push_cast at this
        linarith
      exact_mod_cast this
    have hS₂ : H ≤ S kh := by
      have : ¬ (2 * (h : ℝ) ≤ |(S kh : ℝ) - 2 * kh|) := fun h' => h₂ ⟨hw, h'⟩
      rw [not_le, abs_lt] at this
      have : (H : ℝ) ≤ S kh := by
        have : ((H + 2 * h : ℕ) : ℝ) ≤ ((2 * kh : ℕ) : ℝ) := by exact_mod_cast hkhH
        push_cast at this
        linarith
      exact_mod_cast this
    have hmem : S kh ∈ Word.partialSums w :=
      Word.mem_partialSums.2 ⟨kh, by omega, by omega, rfl⟩
    obtain ⟨u, a, r, hwe, hu, ha⟩ :=
      Word.exists_eq_append_cons_of_lt_mem_partialSums (N := H - 1) hmem (by omega)
    have hcard : Finset.card (Word.exposedPattern (H - 1) w) = u.length := by
      rw [hwe]
      exact Word.card_exposedPattern_append_cons r hu ha
    have hDkh : u.length < kh := by
      by_contra hc
      have htk : w.take kh = u.take kh := by
        rw [hwe, List.take_append_of_le_length (by omega)]
      have : S kh ≤ Word.valSum u := by
        simp only [hS, htk]
        exact Word.valSum_le_of_isPrefix (List.take_prefix _ _)
      omega
    have hDkl : kl ≤ u.length := by
      by_contra hc
      have htk : w.take (u.length + 1) = u ++ [a] := by
        rw [hwe, List.take_append, List.take_of_length_le (by omega)]
        simp
      have hle : S (u.length + 1) ≤ S kl :=
        Word.valSum_le_of_isPrefix (List.take_prefix_take_left (by omega))
      have : S (u.length + 1) = Word.valSum u + a := by
        simp only [hS, htk, Word.valSum_append, Word.valSum_singleton]
      omega
    have hlen : Finset.card (Word.exposedPattern (H - 1) w) < w.length := by omega
    have hoff := Word.off_eq_setOffset_exposedPattern_add hlen
    have hx0 : 0 ≤ ((setOffset (Word.exposedPattern (H - 1) w) : ℚ) : ℝ) := by
      exact_mod_cast setOffset_nonneg _
    have hxJ : ((setOffset (Word.exposedPattern (H - 1) w) : ℚ) : ℝ) < 2 ^ J := by
      have h3 : ¬ ((2 : ℝ) ^ J ≤ (off w : ℝ)) := fun h' => h₃ ⟨hw, h'⟩
      have hle : setOffset (Word.exposedPattern (H - 1) w) ≤ off w := by
        rw [hoff]
        have := off_nonneg (Word.fresh (H - 1) w)
        have : (0 : ℚ) ≤ (3 : ℚ) ^ Finset.card (Word.exposedPattern (H - 1) w) *
            ((2 : ℚ) ^ (H - 1))⁻¹ * off (Word.fresh (H - 1) w) := by positivity
        linarith
      have : ((setOffset (Word.exposedPattern (H - 1) w) : ℚ) : ℝ) ≤ (off w : ℝ) := by
        exact_mod_cast hle
      linarith [not_le.1 h3]
    obtain ⟨j, hj⟩ := exists_mem_mxShShell hx0
    have hjJ : j ≤ J := by
      by_contra hc
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have h1 := le_of_mem_mxShShell_succ hj
      have h2 : (2 : ℝ) ^ J ≤ 2 ^ j' := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    refine mxShSlice_subset_shRetained (d := u.length) (j := j) (by omega) (by omega)
      (by omega) hjJ ⟨hw, ?_⟩
    exact mem_shRetainedHeads.2 ⟨Word.exposedPattern_subset_Icc _ _, hcard, hj⟩
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hm₁ : geomMass E₁ ≤ ENNReal.ofReal (2 * (n : ℝ) ^ (-16 : ℝ)) :=
    geomMass_abs_valSum_take_sub_ge_two_mul_shWidth_le
      (by rw [mxGateLevel_def]; exact hn) (by omega)
  have hm₂ : geomMass E₂ ≤ ENNReal.ofReal (2 * (n : ℝ) ^ (-16 : ℝ)) :=
    geomMass_abs_valSum_take_sub_ge_two_mul_shWidth_le
      (by rw [mxGateLevel_def]; exact hn) hkhle
  have hm₃ : geomMass E₃ ≤ ENNReal.ofReal (7 * (n : ℝ) ^ (-2 : ℝ)) := by
    refine (geomMass_offsetTail_le n (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq := sq_le_two_pow_shJ (n := n) (by omega)
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    push_cast
    gcongr
    linarith
  calc geomMass {w : Word | w.length = n ∧ w ∉ shRetained n}
      ≤ geomMass (E₁ ∪ E₂ ∪ E₃) := geomMass_mono hsub
    _ ≤ geomMass E₁ + geomMass E₂ + geomMass E₃ := by
        refine (geomMass_union_le _ _).trans ?_
        gcongr
        exact geomMass_union_le _ _
    _ ≤ ENNReal.ofReal (2 * (n : ℝ) ^ (-16 : ℝ)) + ENNReal.ofReal (2 * (n : ℝ) ^ (-16 : ℝ)) +
          ENNReal.ofReal (7 * (n : ℝ) ^ (-2 : ℝ)) := by gcongr
    _ = ENNReal.ofReal (7 * (n : ℝ) ^ (-2 : ℝ) + 4 * (n : ℝ) ^ (-16 : ℝ)) := by
        have a : 0 ≤ 2 * (n : ℝ) ^ (-16 : ℝ) := by positivity
        have b : 0 ≤ 7 * (n : ℝ) ^ (-2 : ℝ) := by positivity
        rw [← ENNReal.ofReal_add a a, ← ENNReal.ofReal_add (by positivity) b]
        congr 1
        ring

end CollatzPosDens
