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

Let `s ≥ 1`, let `M` be an `s`-good seed, `n ≥ N_* + N_t`, and let `X` be admissible for
generation `n`. Then the marked mass satisfies `Θ_{n,X}(M) > 2^{-25}`.

The proof chains four estimates. An `s`-good seed is odd with `M > 16^{b_0} s ≥ 16^{b_0}` and
has `Z_{N_*}(M) > 2^{-23}`; the tail bound gives
`Z_n(M) > Z_{N_*}(M) - (47/32) 2^{-24}`; terminal transport and the length-removal bound give
`Θ°_{n,X}(M) ≥ Z_n(M) - E` and `Θ_{n,X}(M) ≥ Θ°_{n,X}(M) - E` with `E = F n^{9/2} ϱ^n`. Since
`n ≥ N_t`, the single term `E` is at most `F ∑_{j ≥ N_t} j^{9/2} ϱ^j < 2^{-30}`. Hence
`Θ_{n,X}(M) > 2^{-23} - (47/32 + 2/64) 2^{-24} = 2^{-25}`.

## Main results

* `CollatzPosDens.two_zpow_neg_twentyFive_lt_markedMass`: `2^{-25} < Θ_{n,X}(M)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Marked mass lower bound**. Let `s ≥ 1`, let `M` be an `s`-good seed,
`n ≥ N_* + N_t`, and let `X` be admissible for generation `n`. Then `Θ_{n,X}(M) > 2^{-25}`. -/
@[collatz_pos_dens "lem_mark_lower"]
theorem two_zpow_neg_twentyFive_lt_markedMass {s M : ℕ} (hM : GoodSeed s M) (hs : 0 < s)
    {n : ℕ} (hn : generationThreshold + terminalThreshold ≤ n) {X : ℝ}
    (hX : IsAdmissibleScale M n X) :
    (2 : ℝ) ^ (-25 : ℤ) < markedMass n X M := by
  have hodd : Odd (M : ℤ) := by exact_mod_cast hM.odd
  have hlow : (16 : ℤ) ^ scale 0 ≤ (M : ℤ) := by exact_mod_cast (hM.sixteen_pow_lt hs).le
  have hcast : ((M : ℤ) : ℚ) = (M : ℚ) := Int.cast_natCast M
  have hNt := terminalThreshold_eq
  have hnt : terminalThreshold ≤ n := by omega
  have hZ := abs_weightedCentralSum_sub_generationThreshold_lt hodd
    (lt_of_lt_of_le (by positivity) hlow) (n := n) (by omega)
  have hT := abs_markedMassUnfiltered_sub_weightedCentralSum_le hodd hlow (n := n)
    (by omega) (X := X) (by rwa [hcast])
  have hL := markedMassUnfiltered_sub_markedMass_le hodd hlow (n := n) (by omega) X
  obtain ⟨hsum, htail⟩ := errorPrefactor_mul_terminalTail_lt
  have hle : (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n ≤
      ∑' j : Set.Ici terminalThreshold,
        ((j : ℕ) : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ (j : ℕ) :=
    hsum.le_tsum (⟨n, hnt⟩ : Set.Ici terminalThreshold) fun j _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg errorDecayRatio_nonneg _)
  have hE : errorPrefactor * (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n <
      (2 : ℝ) ^ (-30 : ℝ) := by
    rw [mul_assoc]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle errorPrefactor_pos.le) htail
  have h23 := hM.lt_weightedCentralSum
  have h30 : (2 : ℝ) ^ (-30 : ℝ) = 2 ^ (-30 : ℤ) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [h30] at hE
  rw [hcast] at hZ hT hL
  rw [abs_lt] at hZ
  rw [abs_le] at hT
  have e1 : (2 : ℝ)⁻¹ ^ 23 = 2 ^ (-23 : ℤ) := by norm_num
  rw [e1] at h23
  have e2 : (2 : ℝ) ^ (-23 : ℤ) = 2 * 2 ^ (-24 : ℤ) := by norm_num
  have e3 : (2 : ℝ) ^ (-25 : ℤ) = 2 ^ (-24 : ℤ) / 2 := by norm_num
  have e4 : (2 : ℝ) ^ (-30 : ℤ) = 2 ^ (-24 : ℤ) / 64 := by norm_num
  rw [e2] at h23
  rw [e4] at hE
  rw [e3]
  set a : ℝ := (2 : ℝ) ^ (-24 : ℤ)
  set Zn := weightedCentralSum n (M : ℚ)
  set Z0 := weightedCentralSum generationThreshold (M : ℚ)
  set U := markedMassUnfiltered n X (M : ℚ)
  set E := errorPrefactor * (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n
  set T := markedMass n X (M : ℚ)
  obtain ⟨hZ1, -⟩ := hZ
  obtain ⟨hT1, -⟩ := hT
  clear_value a Zn Z0 U E T
  have k1 : Zn - 2 * E ≤ T := by linarith
  have k2 : Z0 - 47 / 32 * a < Zn := by linarith
  have k3 : 2 * E < a / 32 := by linarith
  linarith

end CollatzPosDens
