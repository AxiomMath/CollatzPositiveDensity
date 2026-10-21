/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Hpack
public import CollatzPosDens.Transfer.S02OmegaFar
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# The common initial exception allowance `ε_init(ι)`

For a Fourier index `ι ∈ 𝔍 = {o, b}`, the initial exceptional mass is bounded by the rational
`ε_init(ι) := (11/16)^{H_pk(ι)} + 2161 / 2^127 + 148 / Ω_far(ι) ∈ ℚ`, where `H_pk(ι) = Hpack ι`
is the packing expansion length (`35` for `o`, `33` for `b`) and `Ω_far(ι) = omegaFar ι` is the
far-gap threshold. The three summands bound, respectively, the packing loss after `H_pk(ι)`
expansion steps, a fixed dyadic rounding error, and the far-gap contribution.

## Main definitions

* `CollatzPosDens.epsInit`: the allowance `ε_init(ι) ∈ ℚ`.

## Main results

* `CollatzPosDens.epsInit_def`: the defining formula of `ε_init(ι)`.
* `CollatzPosDens.cast_epsInit`: the same formula after casting into a division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.epsInit_pos`: `0 < ε_init(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The common initial exception allowance
`ε_init(ι) := (11/16)^{H_pk(ι)} + 2161 / 2^127 + 148 / Ω_far(ι) ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_eps_init"]
noncomputable def epsInit (ι : FIndex) : ℚ :=
  (11 / 16 : ℚ) ^ Hpack ι + 2161 / 2 ^ 127 + 148 / (omegaFar ι : ℚ)

/-- The defining formula of `ε_init(ι)`. -/
theorem epsInit_def (ι : FIndex) :
    epsInit ι = (11 / 16 : ℚ) ^ Hpack ι + 2161 / 2 ^ 127 + 148 / (omegaFar ι : ℚ) := rfl

/-- The defining formula of `ε_init(ι)`, cast into a division ring of characteristic zero. -/
@[simp, norm_cast]
theorem cast_epsInit {K : Type*} [DivisionRing K] [CharZero K] (ι : FIndex) :
    (epsInit ι : K) =
      (11 / 16 : K) ^ Hpack ι + 2161 / 2 ^ 127 + 148 / (omegaFar ι : K) := by
  rw [epsInit_def, Rat.cast_add, Rat.cast_add, Rat.cast_div, Rat.cast_div, Rat.cast_pow,
    Rat.cast_pow, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_ofNat, Rat.cast_ofNat,
    Rat.cast_ofNat, Rat.cast_ofNat]

/-- `ε_init(ι)` is positive. -/
theorem epsInit_pos (ι : FIndex) : 0 < epsInit ι := by
  rw [epsInit_def]
  have : (0 : ℚ) < omegaFar ι := by exact_mod_cast omegaFar_pos ι
  positivity

end CollatzPosDens
