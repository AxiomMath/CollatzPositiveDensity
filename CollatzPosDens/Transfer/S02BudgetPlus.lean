/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Cont
public import CollatzPosDens.Transfer.S02Epiece
public import CollatzPosDens.Transfer.S02EpieceValue
public import CollatzPosDens.Transfer.S02EpsInit
public import CollatzPosDens.Transfer.S02Eta
public import CollatzPosDens.Transfer.S02PiAdPlus
public import CollatzPosDens.Transfer.S02PW
public import CollatzPosDens.Transfer.S02Qmass
public import CollatzPosDens.Transfer.S02ROmegaValue
public import CollatzPosDens.Transfer.S02ScheduleValues
public import CollatzPosDens.Transfer.S02Ud
public import CollatzPosDens.Transfer.S02Uo
public import CollatzPosDens.Transfer.S02Uv
public import CollatzPosDens.Transfer.S02WeightedSqrt
public import CollatzPosDens.Transfer.S02Xwc

/-!
# The rounded budget `Bud⁺`

The rounded budget is, for each Fourier index `ι ∈ {o, b}`, the rational number
`Bud⁺(ι) = 1/8000 + q_mass / P_W(ι) + (c_cont(ι) - 1/P_W(ι)) (Π⁺_ad(ι) + q_mass η_{r_*(ι)}(ι)
  + 𝓔_sq(ι) + U_o(ι) + ε_init(ι) + q_mass (U_v(ι) + U_d(ι) + E_piece(ι)))`,
built from the paid initial mass `q_mass`, the many-white Taylor sum `P_W(ι)`, the continuation
factor `c_cont(ι)`, the rounded adaptive packing sum `Π⁺_ad(ι)`, the terminal event coefficient
`η_{r_*(ι)}(ι)` (equal to `(77/100)^10` at `o` and to `b_*² = 111160227649/10^12` at `b`), the
weighted square-root allowance `𝓔_sq(ι)`, the deviation errors `U_o(ι), U_v(ι), U_d(ι)`, the
initial exception allowance `ε_init(ι)` and the clearing allowance `E_piece(ι)`. All of these
are explicit rationals, and exact evaluation gives
`1 - Bud⁺(o) = 0.019300993707926079830…` and `1 - Bud⁺(b) = 0.002435391461730373345…`.

## Main definitions

* `CollatzPosDens.budPlus`: the rounded budget `Bud⁺(ι) ∈ ℚ`.

## Main results

* `CollatzPosDens.budPlus_def`: the unfolding of `Bud⁺(ι)`.
* `CollatzPosDens.budPlus_lt_o`: `19300993707926 / 10^15 < 1 - Bud⁺(o)`.
* `CollatzPosDens.budPlus_lt_b`: `2435391461730 / 10^15 < 1 - Bud⁺(b)`.
* `CollatzPosDens.budPlus_gt_o`, `CollatzPosDens.budPlus_gt_b`: the matching upper bounds
  `1 - Bud⁺(o) < 19300993707927 / 10^15` and `1 - Bud⁺(b) < 2435391461731 / 10^15`.
* `CollatzPosDens.budPlus_lt_one`: `Bud⁺(ι) < 1` for both indices.

## Implementation notes

The enclosures of `1 - Bud⁺(ι)` are proved by exact rational arithmetic, one index at a time.
`P_W(ι)` is unfolded into its twenty-one Taylor terms at `x_W(ι)`; `𝓔_sq(ι)` into its `r_*(ι)`
summands, each written through the packing width `B_i(ι)`, the thin-block packing ratio
`ρ_i(ι) = (127/40)(B_i(ι) + H_pk(ι))/A_i(ι)` with `A_i(ι) = b_an S_i(ι) - W(ι, p_i(ι)) - 1`,
`S_i(ι) = K_{*,i}(ι)(p_i(ι) + 1)`, and the schedule positions `p_i(ι)` (read off from
`CollatzPosDens.schedule_values_o` and `CollatzPosDens.schedule_values_b`), divided by `R_Ω(ι)`
(`CollatzPosDens.ROmega_value_o`, `CollatzPosDens.ROmega_value_b`); `ε_init(ι)` through
`Ω_far(ι) = R_Ω(ι)^2`; and `E_piece(ι)` through its value `CollatzPosDens.ePiece_o`,
`CollatzPosDens.ePiece_b`. Then `norm_num` evaluates the resulting closed expression, proving
both sides of the enclosure at once.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The rounded budget
`Bud⁺(ι) := 1/8000 + q_mass / P_W(ι) + (c_cont(ι) - 1/P_W(ι)) (Π⁺_ad(ι) + q_mass η_{r_*(ι)}(ι)
  + 𝓔_sq(ι) + U_o(ι) + ε_init(ι) + q_mass (U_v(ι) + U_d(ι) + E_piece(ι))) ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_budget_plus"]
noncomputable def budPlus (ι : FIndex) : ℚ :=
  1 / 8000 + qMass / PW ι +
    (ccont ι - 1 / PW ι) * (piAdPlus ι + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι +
      epsInit ι + qMass * (Uv ι + Ud ι + ePiece ι))

/-- Unfolding lemma for the rounded budget. -/
theorem budPlus_def (ι : FIndex) : budPlus ι =
    1 / 8000 + qMass / PW ι +
      (ccont ι - 1 / PW ι) * (piAdPlus ι + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι +
        epsInit ι + qMass * (Uv ι + Ud ι + ePiece ι)) :=
  rfl

open Finset in
/-- The two-sided enclosure
`19300993707926 / 10^15 < 1 - Bud⁺(o) < 19300993707927 / 10^15`. -/
private lemma budPlus_o_mem :
    19300993707926 / 10 ^ 15 < 1 - budPlus .o ∧ 1 - budPlus .o < 19300993707927 / 10 ^ 15 := by
  have h := schedule_values_o
  simp only [rStar_o, List.ofFn_succ, List.ofFn_zero, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := h
  simp only [Fin.val_zero, Fin.val_succ, Fin.isValue] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [budPlus_def, eventCoeff_rStar_o, Esq_def, epsInit_def, cast_omegaFar, ROmega_value_o,
    ePiece_o, PW_def, xW_o, rStar_o]
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, eventCoeff_o_eq, packWidth_eq_o,
    thinPackRatio_def, aStar_apply_o, sStar_cast, bAn_eq, qPack_eq, Hpack_o,
    Gammapk_eq, Kstar_o_zero, Kstar_o_one, Kstar_o_two, Kstar_o_three, Kstar_o_four,
    Kstar_o_five, Kstar_o_six, Kstar_o_seven, Kstar_o_eight, Kstar_o_of_nine_le le_rfl,
    qMass_eq, ccont_o, piAdPlus_o, Uo_o, Uv_o, Ud_o]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num

open Finset in
/-- The two-sided enclosure
`2435391461730 / 10^15 < 1 - Bud⁺(b) < 2435391461731 / 10^15`. -/
private lemma budPlus_b_mem :
    2435391461730 / 10 ^ 15 < 1 - budPlus .b ∧ 1 - budPlus .b < 2435391461731 / 10 ^ 15 := by
  have h := schedule_values_b
  simp only [rStar_b, List.ofFn_succ, List.ofFn_zero, List.cons.injEq] at h
  obtain ⟨h0, h1, h2, -, -⟩ := h
  simp only [Fin.val_zero, Fin.val_succ, Fin.isValue] at h0 h1 h2
  rw [budPlus_def, eventCoeff_rStar_b, Esq_def, epsInit_def, cast_omegaFar, ROmega_value_b,
    ePiece_b, PW_def, xW_b, rStar_b]
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, eventCoeff_b_zero, eventCoeff_b_one,
    eventCoeff_b_two, stageRate_eq, packWidth_eq_b, thinPackRatio_def, aStar_apply_b, sStar_cast,
    bAn_eq, qPack_eq, Hpack_b, Gammapk_eq, Kstar_b_zero, Kstar_b_one, Kstar_b_two,
    qMass_eq, ccont_b, piAdPlus_b, Uo_b, Uv_b, Ud_b]
  rw [h0, h1, h2]
  norm_num

/-- The rounded budget at the index `o` leaves the slack
`19300993707926 / 10^15 < 1 - Bud⁺(o)`. -/
@[collatz_pos_dens "lem_s02_budget_plus"]
theorem budPlus_lt_o : 19300993707926 / 10 ^ 15 < 1 - budPlus .o :=
  budPlus_o_mem.1

/-- The rounded budget at the index `b` leaves the slack
`2435391461730 / 10^15 < 1 - Bud⁺(b)`. -/
@[collatz_pos_dens "lem_s02_budget_plus"]
theorem budPlus_lt_b : 2435391461730 / 10 ^ 15 < 1 - budPlus .b :=
  budPlus_b_mem.1

/-- The slack of the rounded budget at the index `o` satisfies
`1 - Bud⁺(o) < 19300993707927 / 10^15`. -/
theorem budPlus_gt_o : 1 - budPlus .o < 19300993707927 / 10 ^ 15 :=
  budPlus_o_mem.2

/-- The slack of the rounded budget at the index `b` satisfies
`1 - Bud⁺(b) < 2435391461731 / 10^15`. -/
theorem budPlus_gt_b : 1 - budPlus .b < 2435391461731 / 10 ^ 15 :=
  budPlus_b_mem.2

/-- The rounded budget is less than one at both Fourier indices. -/
theorem budPlus_lt_one (ι : FIndex) : budPlus ι < 1 := by
  cases ι
  · linarith [budPlus_lt_o]
  · linarith [budPlus_lt_b]

end CollatzPosDens
