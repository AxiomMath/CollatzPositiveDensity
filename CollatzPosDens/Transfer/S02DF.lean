/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dstar

/-!
# The Fourier decay constant `D_F`

At each Fourier parameter index `ι ∈ {o, b}` the Fourier decay constant is the rational number
$$D_F(ι) := 2 D_*(ι) + 6,$$
where `D_*(ι) ∈ ℕ` is the descent threshold `CollatzPosDens.Dstar`, cast to `ℚ`. It is the base
of the Fourier decay bound `|μ̂_n(ξ)| ≤ (D_F(ι) / n)^{A_*(ι)}`.

## Main definitions

* `CollatzPosDens.DF`: the Fourier decay constant `D_F(ι) = 2 D_*(ι) + 6 ∈ ℚ`.

## Main results

* `CollatzPosDens.DF_def`: the defining formula of `D_F(ι)`.
* `CollatzPosDens.cast_DF`: the defining formula cast into a linearly ordered field of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.six_le_DF`, `CollatzPosDens.Dstar_lt_DF`, `CollatzPosDens.DF_pos`:
  elementary bounds `6 ≤ D_F(ι)`, `D_*(ι) < D_F(ι)` and `0 < D_F(ι)`, from `D_*(ι) ∈ ℕ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The Fourier decay constant `D_F(ι) := 2 D_*(ι) + 6 ∈ ℚ`, where `D_*(ι)` is the descent
threshold `Dstar`. -/
@[collatz_pos_dens "def_s02_DF"]
noncomputable def DF (ι : FIndex) : ℚ := 2 * (Dstar ι : ℚ) + 6

/-- The defining formula of `D_F(ι)`. -/
theorem DF_def (ι : FIndex) : DF ι = 2 * (Dstar ι : ℚ) + 6 := rfl

/-- The defining formula of `D_F(ι)`, cast into a linearly ordered field of characteristic
zero. -/
theorem cast_DF {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (ι : FIndex) :
    (DF ι : K) = 2 * (Dstar ι : K) + 6 := by
  rw [DF_def]
  push_cast
  rfl

/-- `6 ≤ D_F(ι)`, as `D_*(ι) ≥ 0`. -/
theorem six_le_DF (ι : FIndex) : 6 ≤ DF ι := by
  have : (0 : ℚ) ≤ Dstar ι := Nat.cast_nonneg _
  rw [DF_def]
  linarith

/-- `D_*(ι) < D_F(ι)`. -/
theorem Dstar_lt_DF (ι : FIndex) : (Dstar ι : ℚ) < DF ι := by
  have : (0 : ℚ) ≤ Dstar ι := Nat.cast_nonneg _
  rw [DF_def]
  linarith

/-- `D_F(ι)` is positive, as `D_F(ι) = 2 D_*(ι) + 6 ≥ 6`. -/
theorem DF_pos (ι : FIndex) : 0 < DF ι :=
  lt_of_lt_of_le (by norm_num) (six_le_DF ι)

end CollatzPosDens
