/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.Schedule

/-!
# The final time `P_*`

The analytic recipe updates its schedule of times `p_0 = p_init, p_1, p_2, …` exactly
`r_*` times. The final time is the natural number
$$P_* := p_{r_*} + 1,$$
one more than the last schedule position. It is a positive integer exceeding every schedule
position `p_i` with `i ≤ r_*`, and in particular exceeds `p_init`.

## Main definitions

* `CollatzPosDens.pStar`: the final time `P_* = p_{r_*} + 1`.

## Main results

* `CollatzPosDens.pStar_def`: the defining formula `P_* = p_{r_*} + 1`.
* `CollatzPosDens.pStar_pos`: `0 < P_*`.
* `CollatzPosDens.one_le_pStar`: `1 ≤ P_*`.
* `CollatzPosDens.schedule_lt_pStar`: `p_i < P_*` for every `i ≤ r_*`.
* `CollatzPosDens.pInit_lt_pStar`: `p_init < P_*`.

## Implementation notes

The number `P_*` has several thousand decimal digits, so `pStar` is irreducible and its body is not
exposed: it is meant to be used only through `pStar_def` and the lemmas of this file.

The body is written as the value at `r = r_*` of the function `r ↦ p_r + 1`. Comparing the
constant `P_*` directly with the closed term `p_{r_*} + 1` makes the kernel try to normalise
`p_{r_*}` to a numeral (it treats `x + 1` as a successor), which does not terminate in practice;
going through the function of a variable `r` keeps that comparison syntactic.

The body is moreover wrapped in `Classical.choose`, on which every kernel's reduction stops. The
body is hidden from importing modules, but a kernel checking the full closure of a later proof
sees it; without the wrapper, any closed arithmetic on `P_*` in such a proof, such as
`S_* = 2^36 P_*` by `rfl`, sends that kernel into evaluating `p_{r_*}`, which does not terminate in
practice.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

public section

namespace CollatzPosDens

/-- The function `r ↦ p_r + 1`. -/
private noncomputable def pStarAux (r : ℕ) : ℕ := schedule r + 1

private theorem pStarAux_def (r : ℕ) : pStarAux r = schedule r + 1 := rfl

/-- The final time `P_* := p_{r_*} + 1`. -/
@[collatz_pos_dens "def_Pstar", irreducible]
noncomputable def pStar : ℕ := Classical.choose (⟨pStarAux rStar, rfl⟩ : ∃ p, p = pStarAux rStar)

/-- The defining formula of `P_*`. -/
theorem pStar_def : pStar = schedule rStar + 1 := by
  delta pStar
  exact (Classical.choose_spec (⟨pStarAux rStar, rfl⟩ : ∃ p, p = pStarAux rStar)).trans
    (pStarAux_def rStar)

/-- `P_*` is positive. -/
theorem pStar_pos : 0 < pStar := by
  rw [pStar_def]; omega

/-- `P_*` is at least `1`. -/
theorem one_le_pStar : 1 ≤ pStar := pStar_pos

/-- `P_*` exceeds every schedule position `p_i` with `i ≤ r_*`. -/
theorem schedule_lt_pStar {i : ℕ} (hi : i ≤ rStar) : schedule i < pStar := by
  rw [pStar_def]; have := schedule_monotone hi; omega

/-- `P_*` exceeds the initial time `p_init`. -/
theorem pInit_lt_pStar : pInit < pStar := by
  have := schedule_lt_pStar (Nat.zero_le rStar)
  rwa [schedule_zero] at this

end CollatzPosDens
