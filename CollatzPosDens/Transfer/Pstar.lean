/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Schedule

/-!
# The final time of the schedule

For `ι : CollatzPosDens.FIndex`, write $p_i(ι)$ for the schedule position
`CollatzPosDens.schedule ι i`, so that $p_0(ι) = p_{init}(ι)$ is `CollatzPosDens.pInit ι`, and
write $r_*(ι)$ for `CollatzPosDens.rStar ι`. The final time `CollatzPosDens.pStar ι` is the
natural number
$$P_*(ι) := p_{r_*(ι)}(ι) + 1,$$
one more than the last schedule position. It is a positive integer exceeding every schedule
position $p_i(ι)$ with $i ≤ r_*(ι)$, and in particular exceeds $p_{init}(ι)$.

## Main definitions

* `CollatzPosDens.pStar`: the final time `P_*(ι) = p_{r_*(ι)}(ι) + 1`.

## Main results

* `CollatzPosDens.pStar_def`: the defining formula `P_*(ι) = p_{r_*(ι)}(ι) + 1`.
* `CollatzPosDens.pStar_pos`: `0 < P_*(ι)`.
* `CollatzPosDens.one_le_pStar`: `1 ≤ P_*(ι)`.
* `CollatzPosDens.schedule_lt_pStar`: `p_i(ι) < P_*(ι)` for every `i ≤ r_*(ι)`.
* `CollatzPosDens.pInit_lt_pStar`: `p_init(ι) < P_*(ι)`.

## Implementation notes

The numbers `P_*(ι)` are far too large to normalise to numerals, so `pStar` is irreducible and
its body is not exposed: it is meant to be used only through `pStar_def` and the lemmas of this
file.

The body is written as the value at `r = r_*(ι)` of the function `r ↦ p_r(ι) + 1`. Comparing the
constant `P_*(ι)` directly with the closed term `p_{r_*(ι)}(ι) + 1` makes the kernel try to
normalise `p_{r_*(ι)}(ι)` to a numeral (it treats `x + 1` as a successor), which does not
terminate in practice; going through the function of a variable `r` keeps that comparison
syntactic.

The body is moreover wrapped in `Classical.choose`, on which every kernel's reduction stops. The
body is hidden from importing modules, but a checker of the full closure sees it; without the
wrapper, any closed arithmetic on `P_*(ι)` in a later proof, such as an identity proved by `rfl`,
sends that checker into evaluating `p_{r_*(ι)}(ι)`, which does not terminate in practice.
-/

public section

namespace CollatzPosDens

/-- The function `r ↦ p_r(ι) + 1`. -/
private noncomputable def pStarAux (ι : FIndex) (r : ℕ) : ℕ := schedule ι r + 1

private theorem pStarAux_def (ι : FIndex) (r : ℕ) : pStarAux ι r = schedule ι r + 1 := rfl

/-- The final time `P_*(ι) := p_{r_*(ι)}(ι) + 1`, one more than the last schedule position
`schedule ι (rStar ι)`. -/
@[collatz_pos_dens "def_Pstar", irreducible]
noncomputable def pStar (ι : FIndex) : ℕ :=
  Classical.choose (⟨pStarAux ι (rStar ι), rfl⟩ : ∃ p, p = pStarAux ι (rStar ι))

/-- The defining formula of `P_*(ι)`. -/
theorem pStar_def (ι : FIndex) : pStar ι = schedule ι (rStar ι) + 1 := by
  delta pStar
  exact (Classical.choose_spec (⟨pStarAux ι (rStar ι), rfl⟩ :
    ∃ p, p = pStarAux ι (rStar ι))).trans (pStarAux_def ι (rStar ι))

/-- `P_*(ι)` is positive. -/
theorem pStar_pos (ι : FIndex) : 0 < pStar ι := by
  rw [pStar_def]
  omega

/-- `P_*(ι)` is at least `1`. -/
theorem one_le_pStar (ι : FIndex) : 1 ≤ pStar ι := pStar_pos ι

/-- `P_*(ι)` exceeds every schedule position `p_i(ι)` with `i ≤ r_*(ι)`. -/
theorem schedule_lt_pStar (ι : FIndex) {i : ℕ} (hi : i ≤ rStar ι) :
    schedule ι i < pStar ι := by
  rw [pStar_def]
  exact Nat.lt_add_one_of_le (schedule_monotone ι hi)

/-- `P_*(ι)` exceeds the initial time `p_init(ι)`. -/
theorem pInit_lt_pStar (ι : FIndex) : pInit ι < pStar ι := by
  simpa [schedule_zero] using schedule_lt_pStar ι (Nat.zero_le (rStar ι))

end CollatzPosDens
