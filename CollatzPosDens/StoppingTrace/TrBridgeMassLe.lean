/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrReward
public import CollatzPosDens.StoppingTrace.TrPathGrowthJ
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass

/-!
# The bridge mass is at most one

Fix a level `n` and a residue `ξ : ResidueGroup n`, and write `ε_*` for `CollatzPosDens.epsStar`
and `γ_*` for `CollatzPosDens.gammaStar`; "black" refers to `(n, ξ, ε_*)`. Let `𝒰(y)` be the set
`CollatzPosDens.trFirstStopSet n ξ ε_* y` of first-stop lists from `y`. For every base point `y`,
the bridge mass `CollatzPosDens.trBridgeMass n ξ y`, that is
`g_br(y) = ∑_{b ∈ 𝒰(y)} bw^⊗(b) e^{-γ_* N^*(y, b; |b|)}`, is at most `1`.

Rewards are nonnegative and `γ_* > 0`, so every tilt factor is at most `1` and
`g_br(y) ≤ ∑_{b ∈ 𝒰(y)} bw^⊗(b)`. A first-stop list `b` ends at a black point, whose
`j`-coordinate is at most `J = ⌊n/2⌋`; since the `j`-coordinate grows by at least one per block,
`j(y) + |b| ≤ J`, so the lengths of the lists in `𝒰(y)` are bounded. The set `𝒰(y)` is
prefix-free, so the Kraft-type inequality for prefix-free families of block lists bounds the
untilted sum by `1`.

## Main results

* `CollatzPosDens.trBridgeMass_le_one_length_le`: a first-stop list `b ∈ 𝒰(y)` has
  `j(y) + |b| ≤ ⌊n/2⌋`.
* `CollatzPosDens.trBridgeMass_le_one`: `g_br(y) ≤ 1`.

## Implementation notes

The bound is usually stated for `y ∈ 𝒫`. The proof only needs the lengths of the lists in `𝒰(y)`
to be bounded, and `|b| ≤ ⌊n/2⌋ - j(y)` holds for every `y ∈ ℤ × ℤ`; so the hypothesis `y ∈ 𝒫`
is dropped and the bound is stated for every `y : ℤ × ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {y : ℤ × ℤ}

/-- A first-stop list `b ∈ 𝒰(y)` satisfies `j(y) + |b| ≤ ⌊n/2⌋`. -/
lemma trBridgeMass_le_one_length_le {b : List (List ℤ × ℤ)} (hb : b ∈ trFirstStopSet n ξ ε y) :
    bkJ y + b.length ≤ ((n / 2 : ℕ) : ℤ) := by
  have hJ := (trFirstStopSet_bkBlack hb).bkJ_le
  have hg := trPath_bkJ_sub_bkJ_ge y b (Nat.zero_le b.length)
  simp only [min_self, Nat.zero_min, trPath_zero] at hg
  push_cast at hg
  linarith

/-- **The bridge mass is at most one**: `g_br(y) ≤ 1` for every base point `y`. -/
@[collatz_pos_dens "lem_tr_bridge_mass_le"]
theorem trBridgeMass_le_one (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) :
    trBridgeMass n ξ y ≤ 1 := by
  refine trBridgeMass_le_tsum_trListWeight.trans ?_
  refine tsum_trListWeight_le_one_of_prefixFree (((n / 2 : ℕ) : ℤ) - bkJ y).toNat _
    (fun u hu b hb ↦ trFirstStopSet_closing_mem hu hb) (fun u hu ↦ ?_)
    isPrefixFree_trFirstStopSet
  have := trBridgeMass_le_one_length_le hu
  omega

/-- The bridge mass is finite. -/
theorem trBridgeMass_ne_top (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) : trBridgeMass n ξ y ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (trBridgeMass_le_one n ξ y)

end CollatzPosDens
