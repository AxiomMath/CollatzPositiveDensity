/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.Recipe.Texp
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Recipe.Erec
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Seed.HistoryPrefix
public import CollatzPosDens.Seed.EndpointUpperGrowth

/-!
# The height of history endpoints

Let `M` be an odd positive integer with `M < 𝓜`. For every `j ≥ 0` and every central history
`h ∈ 𝓗_j(M)`, the endpoint satisfies `R_h ≤ 2^{𝓔(j)} 𝓜`.

The proof is an induction on the generation. Every prefix of a central history is a central
history, so the generation-`i` endpoint `R_i(h)` is a positive odd integer. Each word
`w_i ∈ 𝒞(b_i, K_i)` lies in `𝒲(b_i, r_{b_i}, K_i)`, so by the growth of endpoints it multiplies
the endpoint by at most `2^{K_i + 1} (4/3)^{b_i}`. Since `2^{19} ≤ 3^{12}` we have
`2^{⌊19b/12⌋} ≤ 3^b`, hence `(4/3)^b ≤ 2^{t(b)}`, and `K_i + 1 + t(b_i) = 𝓔(i+1) - 𝓔(i)`.

## Main results

* `CollatzPosDens.historyEndpointAt_le_two_pow_erec_mul`: `R_i(h) ≤ 2^{𝓔(i)} M` for
  `h ∈ 𝓗_n(M)` and `i ≤ n`.
* `CollatzPosDens.historyEndpoint_le_two_pow_erec_mul_seedBound`: `R_h ≤ 2^{𝓔(j)} 𝓜` for
  `h ∈ 𝓗_j(M)`.

## Implementation notes

The source assumes `16^{b_0} ≤ M < 𝓜`; of the lower bound only `0 < M` is used, so the
statement is proved for every odd integer `M` with `0 < M < 𝓜`. The stronger bound
`R_h ≤ 2^{𝓔(j)} M` is proved first.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- From `2^{19} ≤ 3^{12}`: `(4/3)^b ≤ 2^{t(b)}`. -/
private lemma endpointHeight_four_div_three_pow_le (b : ℕ) :
    ((4 : ℚ) / 3) ^ b ≤ 2 ^ texp b := by
  have h1 : 2 ^ (19 * b / 12) ≤ 3 ^ b := two_pow_nineteen_mul_div_twelve_le_three_pow b
  have h2 : (2 : ℚ) ^ texp b * 2 ^ (19 * b / 12) = 4 ^ b := by
    rw [← pow_add, texp_add_div, pow_mul]
    norm_num
  rw [div_pow, div_le_iff₀ (by positivity), ← h2]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h1) (by positivity)

/-- The generation-`i` endpoints (`i ≤ n`) of a central history from a positive odd integer `M`
are nonnegative. -/
private lemma endpointHeight_historyEndpointAt_nonneg {M : ℤ} (hpos : 0 < M) (hodd : Odd M)
    {n : ℕ} {h : Fin n → Word} (hh : h ∈ centralHistories M n) {i : ℕ} (hi : i ≤ n) :
    0 ≤ historyEndpointAt M h i := by
  have hadm := admissible_concatWord_of_mem_centralHistories (centralHistories_prefix hh hi)
  obtain ⟨m, hm, hmpos, -⟩ := hadm.exists_src_eq_pos_odd hpos hodd
  rw [historyEndpointAt_eq_src_concatWord _ _ hi, hm]
  exact_mod_cast hmpos.le

/-- For a central history `h ∈ 𝓗_n(M)` from a positive odd integer `M`, the generation-`i`
endpoint satisfies `R_i(h) ≤ 2^{𝓔(i)} M` for every `i ≤ n`. -/
theorem historyEndpointAt_le_two_pow_erec_mul {M : ℤ} (hpos : 0 < M) (hodd : Odd M) {n : ℕ}
    {h : Fin n → Word} (hh : h ∈ centralHistories M n) {i : ℕ} (hi : i ≤ n) :
    historyEndpointAt M h i ≤ 2 ^ erec i * M := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hin : i < n := hi
    have ih := ih hin.le
    have hR := endpointHeight_historyEndpointAt_nonneg hpos hodd hh hin.le
    have hw := centralFamily_subset_firstCrossing _ _
      (selectedTuples_mem_centralFamily hh.1 ⟨i, hin⟩)
    rw [historyEndpointAt_succ _ h hin]
    have h43 := endpointHeight_four_div_three_pow_le (scale i)
    have hM : (0 : ℚ) ≤ M := by exact_mod_cast hpos.le
    calc src (h ⟨i, hin⟩) (historyEndpointAt M h i)
        ≤ 2 ^ (16 + i / 32 + 1) * (4 / 3) ^ scale i * historyEndpointAt M h i := by
          simpa only [cap_def] using src_le_of_mem_firstCrossing_rb hw hR
      _ ≤ 2 ^ (16 + i / 32 + 1) * 2 ^ texp (scale i) * (2 ^ erec i * M) := by
          gcongr
      _ = 2 ^ erec (i + 1) * M := by
          rw [erec_succ, show erec i + 17 + i / 32 + texp (scale i) =
            (16 + i / 32 + 1) + texp (scale i) + erec i by omega, pow_add, pow_add]
          ring

/-- **Height of endpoints.** Let `M` be odd with `0 < M < 𝓜`. For every `j ≥ 0` and every
central history `h ∈ 𝓗_j(M)`, the endpoint satisfies `R_h ≤ 2^{𝓔(j)} 𝓜`. -/
@[collatz_pos_dens "lem_endpoint_height"]
theorem historyEndpoint_le_two_pow_erec_mul_seedBound {M : ℤ} (hodd : Odd M) (hpos : 0 < M)
    (hM : M < seedBound) {j : ℕ} {h : Fin j → Word} (hh : h ∈ centralHistories M j) :
    historyEndpoint M h ≤ 2 ^ erec j * seedBound := by
  rw [historyEndpoint]
  refine (historyEndpointAt_le_two_pow_erec_mul hpos hodd hh le_rfl).trans ?_
  have : (M : ℚ) ≤ (seedBound : ℕ) := by exact_mod_cast hM.le
  gcongr

end CollatzPosDens
