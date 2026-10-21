/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapLipschitz
public import CollatzPosDens.StoppingTrace.TrCapUpperLem
public import CollatzPosDens.StoppingTrace.TrTreeCertificateCheck
public import Mathlib.Tactic.IntervalCases

/-!
# The capped packet factor near the odd dyadic points

For each quadruple `(c, o, ρ, u)` in the list `(4, 1, 1/24, 9/25)`, `(5, 2, 1/24, 23/50)`,
`(6, 3, 1/24, 14/25)`, `(7, 4, 1/24, 4/5)`, `(4, 1, 1/12, 21/50)`, every odd integer `m` and
every real `β` with `|β| ≤ ρ`, the capped packet factor satisfies
`Φ^cap_c((m + β) / 2^o) < u`.

All frequencies `2^a - 1` of the packet function are integers, so `Φ^cap_c` has period `1` and
only the `2^{o-1}` odd `m` with `0 < m < 2^o` matter. For each such `m` the interval `[-ρ, ρ]` is
covered by `N` closed cells `I_j = [-ρ + 2jρ/N, -ρ + 2(j+1)ρ/N]` with midpoints
`μ_j = -ρ + (2j+1)ρ/N`, `N` chosen per residue. For `β ∈ I_j`, the Lipschitz bound
`|Φ^cap_c(θ) - Φ^cap_c(θ')| ≤ ℓ_c |θ - θ'|` and the value of `Φ^cap_c` at the rational point
`θ_j = (m + μ_j) / 2^o` give `Φ^cap_c((m + β) / 2^o) ≤ Φ^cap_c(θ_j) + ℓ_c 2^{-o} ρ / N`, and the
right side is bounded, at all `70` cells, by the kernel: `Φ^cap_c(θ_j)` through the fixed-point
approximations of `e(2^a θ_j)` of `CollatzPosDens.TrTreeCertificate.capI`.

## Main results

* `CollatzPosDens.trCapFactor_lt_of_cells`: the reduction of the bound
  `Φ^cap_c((m + β) / 2^o) < u` on `|β| ≤ 1/R` to a finite check at the cells of each odd residue.
* `CollatzPosDens.trCapFactor_lt_of_rows`: the same reduction, with real `ρ` and `u`.
* `CollatzPosDens.chPacketFn_gap_one_cells`: the five bounds `Φ^cap_c((m + β) / 2^o) < u`.

## Implementation notes

The value `Φ^cap_c(θ_j)` is bounded in fixed point rather than by the rational majorant
`U^0_c(θ_j)` of `CollatzPosDens.trCapUpper`. This bound is sharper, so few cells suffice: `1`,
`6`, `10` or `16` per odd residue, `70` in all; the cells are checked one odd residue `m` at a
time.
-/

@[expose] public section

namespace CollatzPosDens

open Finset TrTreeCertificate

namespace GapOneCells

/-! ### The cells -/

/-- The midpoint `μ_j = -ρ + (2j+1)ρ/N` of the `j`-th of `N` cells. -/
def mid (ρ : ℚ) (N j : ℕ) : ℚ := -ρ + (2 * j + 1) * ρ / N

/-- The `N` cells cover `[-ρ, ρ]`. -/
theorem exists_abs_sub_mid_le {ρ : ℚ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : |β| ≤ ρ) :
    ∃ j < N, |β - (mid ρ N j : ℝ)| ≤ (ρ : ℝ) / N := by
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hβ₁, hβ₂⟩ := abs_le.mp hβ
  set x : ℝ := (β + ρ) * N / (2 * ρ) with hx
  have hx0 : 0 ≤ x := by
    rw [hx]; apply div_nonneg _ (by positivity); exact mul_nonneg (by linarith) hNR.le
  have hxN : x ≤ N := by
    rw [hx, div_le_iff₀ (by positivity)]; nlinarith
  set j := min ⌊x⌋₊ (N - 1) with hj
  have hjx : (j : ℝ) ≤ x := by
    calc (j : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast min_le_left _ _
      _ ≤ x := Nat.floor_le hx0
  have hxj : x ≤ j + 1 := by
    rcases le_total ⌊x⌋₊ (N - 1) with h | h
    · rw [hj, min_eq_left h]
      exact (Nat.lt_floor_add_one x).le
    · rw [hj, min_eq_right h]
      have : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this]
      linarith
  refine ⟨j, by omega, ?_⟩
  have e : β - (mid ρ N j : ℝ) = (x - j - 1 / 2) * (2 * ρ) / N := by
    rw [hx, mid]; push_cast; field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ρ), abs_of_pos hNR,
    div_le_div_iff_of_pos_right hNR]
  have : |x - j - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  nlinarith

/-- The numerator `N R m + 2 j + 1 - N` of the midpoint `(m + μ_j) / 2^o`, `ρ = 1/R`, over the
denominator `CollatzPosDens.GapOneCells.cellDen`. -/
def cellNum (N R m j : ℕ) : ℤ := N * R * m + 2 * j + 1 - N

/-- The denominator `N R 2^o` of the midpoint `(m + μ_j) / 2^o`, `ρ = 1/R`. -/
def cellDen (N R o : ℕ) : ℕ := N * R * 2 ^ o

/-- The quotient `cellNum N R m j / cellDen N R o` is the midpoint `(m + μ_j) / 2^o` of the
`j`-th of the `N` cells, `ρ = 1/R`. -/
theorem cellNum_div {N R : ℕ} (hN : 0 < N) (hR : 0 < R) (o m j : ℕ) :
    ((cellNum N R m j : ℤ) : ℝ) / ((cellDen N R o : ℕ) : ℝ) =
      ((m : ℝ) + (mid (1 / R) N j : ℝ)) / 2 ^ o := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [cellNum, cellDen, mid]
  push_cast
  field_simp
  ring

/-- The Lipschitz term `⌈ℓ_c 2^{60} / (N R 2^o)⌉`, in units `2^{-60}`. -/
def cellLip (N c o R : ℕ) : ℤ :=
  (lnum c * P + 7 * ((c : ℤ) - 1) * (cellDen N R o : ℤ) - 1) /
    (7 * ((c : ℤ) - 1) * (cellDen N R o : ℤ))

/-- The bound, in units `2^{-60}`, for `Φ^cap_c` on the `j`-th of the `N` cells of the residue
`m`. -/
def cellCap (N c o R m j : ℕ) : ℤ :=
  capI (c - 1) (sumI (c - 1) (chainI (c - 1) (topI (cellNum N R m j) (cellDen N R o)) 116))
    (cellLip N c o R)

/-- The check of the `N` cells of the residue `m` against `u = un / ud`. -/
def rowOK (N c o R : ℕ) (un ud : ℤ) (m : ℕ) : Bool :=
  (List.range N).all fun j => decide (cellCap N c o R m j * ud < un * P)

/-- The capped packet factor has period `1`. -/
private theorem trCapFactor_add_intCast' (c : ℤ) (θ : ℝ) (n : ℤ) :
    trCapFactor c (θ + n) = trCapFactor c θ := by
  unfold trCapFactor
  rw [chPacketFn_add_intCast]

end GapOneCells

open GapOneCells in
/-- Reduction to the cells: if `3 ≤ c ≤ 12`, `1 ≤ o`, `0 < R`, `0 < ud` and, for every odd
`m = 2k + 1 < 2^o` there is `N > 0` such that, for every `j < N`, the cell bound
`cellCap N c o R m j` is below `2^{60} un / ud`, then `Φ^cap_c((m + β) / 2^o) < un / ud` for
every odd integer `m` and every real `β` with `|β| ≤ 1/R`. -/
theorem trCapFactor_lt_of_cells {c : ℕ} (h₁ : 3 ≤ c) (h₂ : c ≤ 12) {o R : ℕ} (ho : 1 ≤ o)
    (hR : 0 < R) {un ud : ℤ} (hud : 0 < ud)
    (hrow : ∀ k < 2 ^ (o - 1), ∃ N, 0 < N ∧ rowOK N c o R un ud (2 * k + 1) = true)
    {m : ℤ} (hm : Odd m) {β : ℝ} (hβ : |β| ≤ 1 / R) :
    trCapFactor c ((m + β) / 2 ^ o) < (un : ℝ) / ud := by
  have hp : (0 : ℤ) < 2 ^ o := by positivity
  set m' := m % 2 ^ o with hm'
  have h0 : 0 ≤ m' := Int.emod_nonneg _ hp.ne'
  have hlt : m' < 2 ^ o := Int.emod_lt_of_pos _ hp
  have hodd : m'.toNat % 2 = 1 := by
    have h2 : (2 : ℤ) ∣ 2 ^ o := dvd_pow_self 2 (by omega)
    have : m' % 2 = 1 := by
      rw [hm', Int.emod_emod_of_dvd _ h2]; exact Int.odd_iff.mp hm
    omega
  have hmlt : m'.toNat < 2 ^ o := by
    have : m'.toNat < (2 ^ o : ℤ).toNat := (Int.toNat_lt_toNat hp).mpr hlt
    simpa using this
  have hdecomp : ((m : ℝ) + β) / 2 ^ o =
      ((m'.toNat : ℝ) + β) / 2 ^ o + ((m / 2 ^ o : ℤ) : ℝ) := by
    have e : (m'.toNat : ℤ) = m' := Int.toNat_of_nonneg h0
    have e2 : ((m'.toNat : ℕ) : ℝ) = ((m' : ℤ) : ℝ) := by exact_mod_cast e
    have e3 : m = m' + 2 ^ o * (m / 2 ^ o) := by
      have := Int.mul_ediv_add_emod m (2 ^ o)
      rw [hm']; linarith
    rw [e2]
    conv_lhs => rw [e3]
    push_cast
    field_simp
    ring
  rw [hdecomp, trCapFactor_add_intCast']
  set n := m'.toNat
  have hρ : (0 : ℚ) < 1 / R := by positivity
  have hpow : 2 ^ o = 2 * 2 ^ (o - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hn : n = 2 * (n / 2) + 1 := by omega
  obtain ⟨N, hN, hrow'⟩ := hrow (n / 2) (by omega)
  rw [← hn] at hrow'
  obtain ⟨j, hj, hβj⟩ := exists_abs_sub_mid_le hρ hN (β := β) (by push_cast; exact hβ)
  have hcell : cellCap N c o R n j * ud < un * P := by
    have := List.all_eq_true.mp hrow' j (List.mem_range.mpr hj)
    simpa using this
  have hden : 0 < cellDen N R o := by unfold cellDen; positivity
  have hgood := chainGoodI_chainI (c - 1) (norm_toCI_topI_sub_le (cellNum N R n j) hden)
  rw [cellNum_div hN hR] at hgood
  have hpo : (0 : ℝ) < 2 ^ o := by positivity
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hdist : |((n : ℝ) + β) / 2 ^ o - ((n : ℝ) + (mid (1 / R) N j : ℝ)) / 2 ^ o| ≤
      1 / ((cellDen N R o : ℕ) : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hpo, div_le_iff₀ hpo]
    calc |(n : ℝ) + β - (n + (mid (1 / R) N j : ℝ))| = |β - (mid (1 / R) N j : ℝ)| := by ring_nf
      _ ≤ ((1 / R : ℚ) : ℝ) / N := hβj
      _ = _ := by simp only [cellDen]; push_cast; field_simp
  have hlip : (trLipConst c : ℝ) *
      |((n : ℝ) + β) / 2 ^ o - ((n : ℝ) + (mid (1 / R) N j : ℝ)) / 2 ^ o| ≤
        (cellLip N c o R : ℝ) / 2 ^ 60 := by
    have hc1 : (0 : ℝ) < (c : ℝ) - 1 := by
      have : (3 : ℝ) ≤ c := by exact_mod_cast h₁
      linarith
    have hD : (0 : ℤ) < 7 * ((c : ℤ) - 1) * (cellDen N R o : ℤ) := by
      have : (3 : ℤ) ≤ c := by exact_mod_cast h₁
      have : (0 : ℤ) < (cellDen N R o : ℤ) := by exact_mod_cast hden
      nlinarith
    have hceil := div_le_ceil_ediv (lnum c * P) _ hD
    have hl0 : (0 : ℝ) ≤ trLipConst c := by exact_mod_cast trLipConst_nonneg c
    calc (trLipConst c : ℝ) *
          |((n : ℝ) + β) / 2 ^ o - ((n : ℝ) + (mid (1 / R) N j : ℝ)) / 2 ^ o|
        ≤ (trLipConst c : ℝ) * (1 / ((cellDen N R o : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hdist hl0
      _ = ((lnum c * P : ℤ) : ℝ) / ((7 * ((c : ℤ) - 1) * (cellDen N R o : ℤ) : ℤ) : ℝ) /
            2 ^ 60 := by
          rw [trLipConst_eq_lnum h₁ h₂]
          push_cast [cast_P]
          field_simp
      _ ≤ (cellLip N c o R : ℝ) / 2 ^ 60 := div_le_div_of_nonneg_right hceil (by positivity)
  have hb := trCapFactor_le_capI h₁ (by omega) hgood hlip
  have hcellR : ((cellCap N c o R n j : ℤ) : ℝ) * ud < (un : ℝ) * 2 ^ 60 := by
    have := (Int.cast_lt (R := ℝ)).mpr hcell
    push_cast [cast_P] at this
    exact this
  have hudR : (0 : ℝ) < ud := by exact_mod_cast hud
  rw [lt_div_iff₀ hudR]
  have hb' : trCapFactor c (((n : ℝ) + β) / 2 ^ o) ≤ (cellCap N c o R n j : ℝ) / 2 ^ 60 := hb
  calc trCapFactor c (((n : ℝ) + β) / 2 ^ o) * ud ≤ (cellCap N c o R n j : ℝ) / 2 ^ 60 * ud :=
        mul_le_mul_of_nonneg_right hb' hudR.le
    _ < un := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        exact hcellR

namespace GapOneCells

/-- The 10 cells of the residue `m = 1` pass the check for `c = 4`, `o = 1`, `ρ = 1/24`,
`u = 9/25`. -/
theorem rowOK_four_one_m1 : rowOK 10 4 1 24 9 25 1 = true := by decide +kernel

/-- The 6 cells of the residue `m = 1` pass the check for `c = 5`, `o = 2`, `ρ = 1/24`,
`u = 23/50`. -/
theorem rowOK_five_two_m1 : rowOK 6 5 2 24 23 50 1 = true := by decide +kernel

/-- The 6 cells of the residue `m = 3` pass the check for `c = 5`, `o = 2`, `ρ = 1/24`,
`u = 23/50`. -/
theorem rowOK_five_two_m3 : rowOK 6 5 2 24 23 50 3 = true := by decide +kernel

/-- The 16 cells of the residue `m = 1` pass the check for `c = 6`, `o = 3`, `ρ = 1/24`,
`u = 14/25`. -/
theorem rowOK_six_three_m1 : rowOK 16 6 3 24 14 25 1 = true := by decide +kernel

/-- The single cell of the residue `m = 3` passes the check for `c = 6`, `o = 3`, `ρ = 1/24`,
`u = 14/25`. -/
theorem rowOK_six_three_m3 : rowOK 1 6 3 24 14 25 3 = true := by decide +kernel

/-- The single cell of the residue `m = 5` passes the check for `c = 6`, `o = 3`, `ρ = 1/24`,
`u = 14/25`. -/
theorem rowOK_six_three_m5 : rowOK 1 6 3 24 14 25 5 = true := by decide +kernel

/-- The 16 cells of the residue `m = 7` pass the check for `c = 6`, `o = 3`, `ρ = 1/24`,
`u = 14/25`. -/
theorem rowOK_six_three_m7 : rowOK 16 6 3 24 14 25 7 = true := by decide +kernel

/-- The single cell of the residue `m = 1` passes the check for `c = 7`, `o = 4`, `ρ = 1/24`,
`u = 4/5`. -/
theorem rowOK_seven_four_m1 : rowOK 1 7 4 24 4 5 1 = true := by decide +kernel

/-- The single cell of the residue `m = 3` passes the check for `c = 7`, `o = 4`, `ρ = 1/24`,
`u = 4/5`. -/
theorem rowOK_seven_four_m3 : rowOK 1 7 4 24 4 5 3 = true := by decide +kernel

/-- The single cell of the residue `m = 5` passes the check for `c = 7`, `o = 4`, `ρ = 1/24`,
`u = 4/5`. -/
theorem rowOK_seven_four_m5 : rowOK 1 7 4 24 4 5 5 = true := by decide +kernel

/-- The single cell of the residue `m = 7` passes the check for `c = 7`, `o = 4`, `ρ = 1/24`,
`u = 4/5`. -/
theorem rowOK_seven_four_m7 : rowOK 1 7 4 24 4 5 7 = true := by decide +kernel

/-- The single cell of the residue `m = 9` passes the check for `c = 7`, `o = 4`, `ρ = 1/24`,
`u = 4/5`. -/
theorem rowOK_seven_four_m9 : rowOK 1 7 4 24 4 5 9 = true := by decide +kernel

/-- The single cell of the residue `m = 11` passes the check for `c = 7`, `o = 4`, `ρ = 1/24`,
`u = 4/5`. -/
theorem rowOK_seven_four_m11 : rowOK 1 7 4 24 4 5 11 = true := by decide +kernel

/-- The single cell of the residue `m = 13` passes the check for `c = 7`, `o = 4`, `ρ = 1/24`,
`u = 4/5`. -/
theorem rowOK_seven_four_m13 : rowOK 1 7 4 24 4 5 13 = true := by decide +kernel

/-- The single cell of the residue `m = 15` passes the check for `c = 7`, `o = 4`, `ρ = 1/24`,
`u = 4/5`. -/
theorem rowOK_seven_four_m15 : rowOK 1 7 4 24 4 5 15 = true := by decide +kernel

/-- The 6 cells of the residue `m = 1` pass the check for `c = 4`, `o = 1`, `ρ = 1/12`,
`u = 21/50`. -/
theorem rowOK_four_one_wide_m1 : rowOK 6 4 1 12 21 50 1 = true := by decide +kernel

end GapOneCells

/-- One quadruple: from the rows of cells to the bound with real `ρ` and `u`. -/
theorem trCapFactor_lt_of_rows {c : ℕ} (h₁ : 3 ≤ c) (h₂ : c ≤ 12) {o R : ℕ} (ho : 1 ≤ o)
    (hR : 0 < R) {un ud : ℤ} (hud : 0 < ud)
    (hrow : ∀ k < 2 ^ (o - 1), ∃ N, 0 < N ∧ GapOneCells.rowOK N c o R un ud (2 * k + 1) = true)
    {ρ' u' : ℝ} (hρ' : 1 / (R : ℝ) = ρ') (hu' : (un : ℝ) / ud = u')
    {m : ℤ} (hm : Odd m) {β : ℝ} (hβ : |β| ≤ ρ') :
    trCapFactor c ((m + β) / 2 ^ o) < u' :=
  hu' ▸ trCapFactor_lt_of_cells h₁ h₂ ho hR hud hrow hm (hρ' ▸ hβ)

open GapOneCells in
/-- **Full-character bounds on narrow cells.** For every quadruple `(c, o, ρ, u)` in the list
`(4, 1, 1/24, 9/25)`, `(5, 2, 1/24, 23/50)`, `(6, 3, 1/24, 14/25)`, `(7, 4, 1/24, 4/5)`,
`(4, 1, 1/12, 21/50)`, every odd integer `m` and every real `β` with `|β| ≤ ρ`,
`Φ^cap_c((m + β) / 2^o) < u`. -/
@[collatz_pos_dens "lem_tr_gap_one_cells"]
theorem chPacketFn_gap_one_cells :
    ∀ q ∈ ([(4, 1, 1 / 24, 9 / 25), (5, 2, 1 / 24, 23 / 50), (6, 3, 1 / 24, 14 / 25),
      (7, 4, 1 / 24, 4 / 5), (4, 1, 1 / 12, 21 / 50)] : List (ℤ × ℕ × ℝ × ℝ)),
      ∀ m : ℤ, Odd m → ∀ β : ℝ, |β| ≤ q.2.2.1 →
        trCapFactor q.1 ((m + β) / 2 ^ q.2.1) < q.2.2.2 := by
  intro q hq m hm β hβ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · have := trCapFactor_lt_of_rows (c := 4) (o := 1) (R := 24) (un := 9) (ud := 25)
      (ρ' := 1 / 24) (u' := 9 / 25) (by norm_num)
      (by norm_num) le_rfl (by norm_num) (by norm_num) (fun k hk => ?_) (by norm_num)
      (by norm_num) hm hβ
    · exact_mod_cast this
    interval_cases k
    exact ⟨10, by norm_num, rowOK_four_one_m1⟩
  · have := trCapFactor_lt_of_rows (c := 5) (o := 2) (R := 24) (un := 23) (ud := 50)
      (ρ' := 1 / 24) (u' := 23 / 50) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k hk => ?_) (by norm_num)
      (by norm_num) hm hβ
    · exact_mod_cast this
    interval_cases k
    · exact ⟨6, by norm_num, rowOK_five_two_m1⟩
    · exact ⟨6, by norm_num, rowOK_five_two_m3⟩
  · have := trCapFactor_lt_of_rows (c := 6) (o := 3) (R := 24) (un := 14) (ud := 25)
      (ρ' := 1 / 24) (u' := 14 / 25) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k hk => ?_) (by norm_num)
      (by norm_num) hm hβ
    · exact_mod_cast this
    interval_cases k
    · exact ⟨16, by norm_num, rowOK_six_three_m1⟩
    · exact ⟨1, by norm_num, rowOK_six_three_m3⟩
    · exact ⟨1, by norm_num, rowOK_six_three_m5⟩
    · exact ⟨16, by norm_num, rowOK_six_three_m7⟩
  · have := trCapFactor_lt_of_rows (c := 7) (o := 4) (R := 24) (un := 4) (ud := 5)
      (ρ' := 1 / 24) (u' := 4 / 5) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun k hk => ?_) (by norm_num)
      (by norm_num) hm hβ
    · exact_mod_cast this
    interval_cases k
    · exact ⟨1, by norm_num, rowOK_seven_four_m1⟩
    · exact ⟨1, by norm_num, rowOK_seven_four_m3⟩
    · exact ⟨1, by norm_num, rowOK_seven_four_m5⟩
    · exact ⟨1, by norm_num, rowOK_seven_four_m7⟩
    · exact ⟨1, by norm_num, rowOK_seven_four_m9⟩
    · exact ⟨1, by norm_num, rowOK_seven_four_m11⟩
    · exact ⟨1, by norm_num, rowOK_seven_four_m13⟩
    · exact ⟨1, by norm_num, rowOK_seven_four_m15⟩
  · have := trCapFactor_lt_of_rows (c := 4) (o := 1) (R := 12) (un := 21) (ud := 50)
      (ρ' := 1 / 12) (u' := 21 / 50) (by norm_num)
      (by norm_num) le_rfl (by norm_num) (by norm_num) (fun k hk => ?_) (by norm_num)
      (by norm_num) hm hβ
    · exact_mod_cast this
    interval_cases k
    exact ⟨6, by norm_num, rowOK_four_one_wide_m1⟩

end CollatzPosDens
