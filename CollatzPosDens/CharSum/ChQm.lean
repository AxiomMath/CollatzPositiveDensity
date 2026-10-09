/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChDist

/-!
# Weighted suprema of `Q` near the cut-off

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For a real exponent `A ≥ 0` and an
integer `m ≥ 0`, the weighted supremum of the renewal function near the cut-off is
`Q_m = sup {d_J(p)^A Q(p) : p ∈ 𝒫, j(p) ≥ ⌊n/2⌋ ∸ m}`.

## Main definitions

* `CollatzPosDens.chQm n ξ ε A m`: the weighted supremum `Q_m`.

## Main results

* `CollatzPosDens.chQm_nonempty`: the set defining `Q_m` is nonempty.
* `CollatzPosDens.le_chQm`: each weighted value `d_J(p)^A Q(p)` in range is at most `Q_m`,
  provided the set of such values is bounded above.
* `CollatzPosDens.chQm_le`: `Q_m ≤ B` whenever every weighted value in range is at most `B`.

## Implementation notes

The supremum is the conditionally complete supremum `sSup` in `ℝ`, and the power `d_J(p)^A` is
the real power `Real.rpow` of the positive base `d_J(p) ≥ 1`. The exponent `A` ranges over all
of `ℝ`, rather than only `A ≥ 0`. The truncated difference `⌊n/2⌋ ∸ m` is natural number
subtraction. The index set is never empty (it contains `(max ⌊n/2⌋ 1, 0)`); boundedness above
is a hypothesis of `CollatzPosDens.le_chQm`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- The weighted supremum `Q_m = sup {d_J(p)^A Q(p) : p ∈ 𝒫, j(p) ≥ ⌊n/2⌋ ∸ m}` of the renewal
function near the cut-off. -/
@[collatz_pos_dens "def_ch_Qm"]
noncomputable def chQm (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (A : ℝ) (m : ℕ) : ℝ :=
  sSup {x | ∃ p ∈ bkPoints, ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p ∧
    x = (chDist n p : ℝ) ^ A * chQ n ξ ε p}

/-- `chQm n ξ ε A m` is the supremum of `d_J(p)^A Q(p)` over `p ∈ 𝒫` with `j(p) ≥ ⌊n/2⌋ ∸ m`. -/
theorem chQm_def (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (A : ℝ) (m : ℕ) :
    chQm n ξ ε A m = sSup {x | ∃ p ∈ bkPoints, ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p ∧
      x = (chDist n p : ℝ) ^ A * chQ n ξ ε p} :=
  rfl

/-- The set `{d_J(p)^A Q(p) : p ∈ 𝒫, j(p) ≥ ⌊n/2⌋ ∸ m}` whose supremum defines `Q_m` is
nonempty: it contains the value at `(max ⌊n/2⌋ 1, 0)`. -/
theorem chQm_nonempty (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (A : ℝ) (m : ℕ) :
    {x | ∃ p ∈ bkPoints, ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p ∧
      x = (chDist n p : ℝ) ^ A * chQ n ξ ε p}.Nonempty := by
  refine ⟨_, (((max (n / 2) 1 : ℕ) : ℤ), 0), ?_, ?_, rfl⟩
  · simp only [mem_bkPoints, bkJ]; omega
  · simp only [bkJ]; omega

/-- Each weighted value `d_J(p)^A Q(p)` with `p ∈ 𝒫` and `j(p) ≥ ⌊n/2⌋ ∸ m` is at most `Q_m`,
provided these values are bounded above. -/
theorem le_chQm {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {A : ℝ} {m : ℕ}
    (hbdd : BddAbove {x | ∃ p ∈ bkPoints, ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p ∧
      x = (chDist n p : ℝ) ^ A * chQ n ξ ε p})
    {p : ℤ × ℤ} (hp : p ∈ bkPoints) (hj : ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p) :
    (chDist n p : ℝ) ^ A * chQ n ξ ε p ≤ chQm n ξ ε A m :=
  le_csSup hbdd ⟨p, hp, hj, rfl⟩

/-- `Q_m ≤ B` whenever `d_J(p)^A Q(p) ≤ B` for every `p ∈ 𝒫` with `j(p) ≥ ⌊n/2⌋ ∸ m`. -/
theorem chQm_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {A : ℝ} {m : ℕ} {B : ℝ}
    (h : ∀ p ∈ bkPoints, ((n / 2 - m : ℕ) : ℤ) ≤ bkJ p →
      (chDist n p : ℝ) ^ A * chQ n ξ ε p ≤ B) :
    chQm n ξ ε A m ≤ B :=
  csSup_le (chQm_nonempty n ξ ε A m) fun _ ⟨p, hp, hj, hx⟩ => hx ▸ h p hp hj

end CollatzPosDens
