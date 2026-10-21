/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Dbad
public import CollatzPosDens.Transfer.S02Dsc

/-!
# The descent threshold `D_*`

At each Fourier parameter index `ι ∈ {o, b}` the descent threshold is the natural number
$$D_*(ι) := \max\bigl(D_{\mathrm{bad}}(ι),\ D_{\mathrm{sc}}(ι)\bigr),$$
the maximum of the bad-advance threshold `D_bad(ι)` and the scale threshold `D_sc(ι)`. It
dominates both entries; in particular `D_*(ι) ≥ D_bad(ι) ≥ 2^43`.

## Main definitions

* `CollatzPosDens.Dstar`: the descent threshold `D_*(ι) ∈ ℕ`.

## Main results

* `CollatzPosDens.Dstar_def`: the defining formula of `D_*(ι)`.
* `CollatzPosDens.cast_Dstar`: the defining formula cast into a linearly ordered semiring,
  e.g. `ℚ` or `ℝ`.
* `CollatzPosDens.Dbad_le_Dstar`, `CollatzPosDens.Dsc_le_Dstar`: each entry of the maximum is at
  most `D_*(ι)`.
* `CollatzPosDens.two_pow_43_le_Dstar`, `CollatzPosDens.two_le_Dstar`,
  `CollatzPosDens.one_le_Dstar`, `CollatzPosDens.Dstar_pos`: lower bounds, from
  `D_*(ι) ≥ D_bad(ι) ≥ 2^43`.
* `CollatzPosDens.Dstar_le_iff`: a characterisation of upper bounds for `D_*(ι)`.

## Implementation notes

Since `D_bad(ι)` and `D_sc(ι)` are built from the final time `P_*(ι)` and the far-gap threshold
`Ω_far(ι)`, closed numbers far too large to normalise, `D_*` is irreducible and is used only
through the lemmas of this file, never by evaluation.
-/

@[expose] public section

namespace CollatzPosDens

/-- The descent threshold `D_*(ι) := max (D_bad(ι), D_sc(ι)) ∈ ℕ`. -/
@[collatz_pos_dens "def_Dstar", irreducible]
noncomputable def Dstar (ι : FIndex) : ℕ :=
  max (Dbad ι) (Dsc ι)

/-- The defining formula of `D_*(ι)`. -/
theorem Dstar_def (ι : FIndex) : Dstar ι = max (Dbad ι) (Dsc ι) := by
  unfold Dstar
  rfl

/-- A natural number bounds `D_*(ι)` from above iff it bounds both entries of the maximum. -/
theorem Dstar_le_iff {ι : FIndex} {x : ℕ} : Dstar ι ≤ x ↔ Dbad ι ≤ x ∧ Dsc ι ≤ x := by
  simp only [Dstar_def, max_le_iff]

/-- The defining formula of `D_*(ι)`, cast into a linearly ordered semiring. -/
theorem cast_Dstar {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    (ι : FIndex) : (Dstar ι : R) = max (Dbad ι : R) (Dsc ι : R) := by
  rw [Dstar_def, Nat.cast_max]

/-- `D_bad(ι) ≤ D_*(ι)`. -/
theorem Dbad_le_Dstar (ι : FIndex) : Dbad ι ≤ Dstar ι := (Dstar_le_iff.1 le_rfl).1

/-- `D_sc(ι) ≤ D_*(ι)`. -/
theorem Dsc_le_Dstar (ι : FIndex) : Dsc ι ≤ Dstar ι := (Dstar_le_iff.1 le_rfl).2

/-- `2 ^ 43 ≤ D_*(ι)`, from `D_*(ι) ≥ D_bad(ι) ≥ 2^43`. -/
theorem two_pow_43_le_Dstar (ι : FIndex) : 2 ^ 43 ≤ Dstar ι :=
  (two_pow_43_le_Dbad ι).trans (Dbad_le_Dstar ι)

/-- `2 ≤ D_*(ι)`. -/
theorem two_le_Dstar (ι : FIndex) : 2 ≤ Dstar ι :=
  le_trans (by norm_num) (two_pow_43_le_Dstar ι)

/-- `1 ≤ D_*(ι)`. -/
theorem one_le_Dstar (ι : FIndex) : 1 ≤ Dstar ι := one_le_two.trans (two_le_Dstar ι)

/-- `D_*(ι)` is positive. -/
theorem Dstar_pos (ι : FIndex) : 0 < Dstar ι := lt_of_lt_of_le two_pos (two_le_Dstar ι)

end CollatzPosDens
