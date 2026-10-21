/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Cont
public import CollatzPosDens.Transfer.S02Epiece
public import CollatzPosDens.Transfer.S02EpsInit
public import CollatzPosDens.Transfer.S02Eta
public import CollatzPosDens.Transfer.S02PiAd
public import CollatzPosDens.Transfer.S02PW
public import CollatzPosDens.Transfer.S02Qmass
public import CollatzPosDens.Transfer.S02Ud
public import CollatzPosDens.Transfer.S02Uo
public import CollatzPosDens.Transfer.S02Uv
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02WeightedSqrt

/-!
# The budget `Bud`

This file defines, for each Fourier index `ι ∈ {o, b}`, the rational number
`Bud(ι) = 1/8000 + q_mass / P_W(ι) + (c_cont(ι) - 1/P_W(ι)) (Π_ad(ι) + q_mass η_{r_*(ι)}(ι)
  + 𝓔_sq(ι) + U_o(ι) + ε_init(ι) + q_mass (U_v(ι) + U_d(ι) + E_piece(ι)))`,
built from the constants `qMass`, `PW`, `ccont`, `piAd`, `eventCoeff`, `rStar`, `Esq`, `Uo`,
`epsInit`, `Uv`, `Ud` and `ePiece`, and proves that it is positive.

## Main definitions

* `CollatzPosDens.Bud`: the budget `Bud(ι)`, a rational number.

## Main results

* `CollatzPosDens.Bud_def`: the unfolding of `Bud(ι)`.
* `CollatzPosDens.Bud_cast`: the cast of `Bud(ι)` into a division ring of characteristic zero,
  e.g. `ℝ`, is the same expression in the cast constants.
* `CollatzPosDens.ccont_sub_inv_PW_pos`: the continuation factor `c_cont(ι) - 1/P_W(ι)` is
  positive.
* `CollatzPosDens.Bud_pos`: `0 < Bud(ι)`.

## Implementation notes

`Bud` is `noncomputable` only because some of its constituents (`𝓔_sq`, `ε_init`, `E_piece`)
are; each `Bud(ι)` is nevertheless a closed rational number.
-/

@[expose] public section

namespace CollatzPosDens

/-- The budget
`Bud(ι) := 1/8000 + q_mass / P_W(ι) + (c_cont(ι) - 1/P_W(ι)) (Π_ad(ι) + q_mass η_{r_*(ι)}(ι)
  + 𝓔_sq(ι) + U_o(ι) + ε_init(ι) + q_mass (U_v(ι) + U_d(ι) + E_piece(ι))) ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_budget"]
noncomputable def Bud (ι : FIndex) : ℚ :=
  1 / 8000 + qMass / PW ι +
    (ccont ι - 1 / PW ι) * (piAd ι + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι + epsInit ι +
      qMass * (Uv ι + Ud ι + ePiece ι))

/-- Unfolding lemma for the budget. -/
theorem Bud_def (ι : FIndex) : Bud ι =
    1 / 8000 + qMass / PW ι +
      (ccont ι - 1 / PW ι) * (piAd ι + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι + epsInit ι +
        qMass * (Uv ι + Ud ι + ePiece ι)) := rfl

/-- The cast of the budget into a division ring of characteristic zero. -/
theorem Bud_cast {K : Type*} [DivisionRing K] [CharZero K] (ι : FIndex) :
    (Bud ι : K) =
      1 / 8000 + (qMass : K) / (PW ι : K) +
        ((ccont ι : K) - 1 / (PW ι : K)) *
          ((piAd ι : K) + (qMass : K) * (eventCoeff ι (rStar ι) : K) + (Esq ι : K) + (Uo ι : K) +
            (epsInit ι : K) + (qMass : K) * ((Uv ι : K) + (Ud ι : K) + (ePiece ι : K))) := by
  rw [Bud_def]
  push_cast
  rfl

/-- The continuation factor `c_cont(ι) - 1/P_W(ι)` of the budget is positive. -/
theorem ccont_sub_inv_PW_pos (ι : FIndex) : 0 < ccont ι - 1 / PW ι := by
  have h : 1 / PW ι ≤ 1 := by
    rw [div_le_one (PW_pos ι)]
    exact one_le_PW ι
  linarith [one_lt_ccont ι]

/-- The budget is positive. -/
theorem Bud_pos (ι : FIndex) : 0 < Bud ι := by
  have := ccont_sub_inv_PW_pos ι
  have := qMass_pos
  have := PW_pos ι
  have := piAd_pos ι
  have := eventCoeff_pos ι (rStar ι)
  have := Esq_pos ι
  have := Uo_pos ι
  have := epsInit_pos ι
  have := Uv_pos ι
  have := Ud_pos ι
  have := ePiece_nonneg ι
  rw [Bud_def]
  positivity

end CollatzPosDens
