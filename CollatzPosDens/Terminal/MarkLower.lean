/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.F
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.Nt
public import CollatzPosDens.Recipe.NtTerm
public import CollatzPosDens.Recipe.NtValue
public import CollatzPosDens.Recipe.Varrho
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.ZTail
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.MarkedMass
public import CollatzPosDens.Terminal.MarkedMassUnfiltered
public import CollatzPosDens.Terminal.LengthRemoved
public import CollatzPosDens.Terminal.TerminalTransport

/-!
# Lower bound for the marked mass

Let `M` be a good seed, `n ≥ N_* + N_t`, and let `X` be admissible for generation `n`. Then the
marked mass satisfies `Θ_{n,X}(M) > 2^{-25}`.

The proof chains four estimates. A good seed has `Z_{N_*}(M) > 2^{-23}`; the tail bound gives
`Z_n(M) > Z_{N_*}(M) - (47/32) 2^{-24}`; terminal transport and the length-removal bound give
`Θ°_{n,X}(M) ≥ Z_n(M) - E` and `Θ_{n,X}(M) ≥ Θ°_{n,X}(M) - E` with `E = F n^{9/2} ϱ^n`. Since
`n ≥ N_t`, the single term `E` is at most `F ∑_{j ≥ N_t} j^{9/2} ϱ^j < 2^{-30}`. Hence
`Θ_{n,X}(M) > 2^{-23} - (47/32 + 2/64) 2^{-24} = 2^{-25}`.

## Main results

* `CollatzPosDens.two_zpow_neg_twentyFive_lt_markedMass`: `2^{-25} < Θ_{n,X}(M)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Marked mass lower bound**. Let `M` be a good seed, `n ≥ N_* + N_t`, and let `X` be
admissible for generation `n`. Then `Θ_{n,X}(M) > 2^{-25}`. -/
@[collatz_pos_dens "lem_mark_lower"]
theorem two_zpow_neg_twentyFive_lt_markedMass {M : ℕ} (hM : GoodSeed M) {n : ℕ}
    (hn : generationThreshold + terminalThreshold ≤ n) {X : ℝ}
    (hX : IsAdmissibleScale M n X) :
    (2 : ℝ) ^ (-25 : ℤ) < markedMass n X M := by
  have hodd : Odd (M : ℤ) := by exact_mod_cast hM.odd
  have hlow : (16 : ℤ) ^ scale 0 ≤ (M : ℤ) := by exact_mod_cast hM.lower.le
  have hcast : ((M : ℤ) : ℚ) = (M : ℚ) := Int.cast_natCast M
  have hNt := terminalThreshold_eq
  have hnt : terminalThreshold ≤ n := by omega
  have hZ := abs_weightedCentralSum_sub_generationThreshold_lt hodd
    (lt_of_lt_of_le (by positivity) hlow) (n := n) (by omega)
  have hT := abs_markedMassUnfiltered_sub_weightedCentralSum_le hodd hlow (n := n)
    (by omega) (X := X) (by rwa [hcast])
  have hL := markedMassUnfiltered_sub_markedMass_le hodd hlow (n := n) (by omega) X
  obtain ⟨hs, htail⟩ := errorPrefactor_mul_terminalTail_lt
  have hle : (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n ≤
      ∑' j : Set.Ici terminalThreshold,
        ((j : ℕ) : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ (j : ℕ) :=
    hs.le_tsum (⟨n, hnt⟩ : Set.Ici terminalThreshold) fun j _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg errorDecayRatio_nonneg _)
  have hE : errorPrefactor * (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n <
      (2 : ℝ) ^ (-30 : ℝ) := by
    rw [mul_assoc]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle errorPrefactor_pos.le) htail
  have h23 := hM.lt_weightedCentralSum
  rw [show (2 : ℝ) ^ (-30 : ℝ) = 2 ^ (-24 : ℤ) / 64 by rw [← Real.rpow_intCast]; norm_num] at hE
  rw [show (2 : ℝ)⁻¹ ^ 23 = 2 * 2 ^ (-24 : ℤ) by norm_num] at h23
  rw [show (2 : ℝ) ^ (-25 : ℤ) = 2 ^ (-24 : ℤ) / 2 by norm_num]
  rw [hcast] at hZ hT hL
  set a : ℝ := (2 : ℝ) ^ (-24 : ℤ)
  set E := errorPrefactor * (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n
  clear_value a E
  linarith [(abs_lt.1 hZ).1, (abs_le.1 hT).1]

end CollatzPosDens
