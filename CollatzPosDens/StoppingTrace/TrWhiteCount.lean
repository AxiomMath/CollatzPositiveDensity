/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrFreshLaw

/-!
# The weighted white count of a fresh atom

Fix a level `n ≥ 1` and a residue `ξ ∈ G_n`. For an entry point `e ∈ 𝒫`, a fresh atom
`a = ((r, ℓ), β) ∈ 𝒜_n` and a time `p ∈ ℕ`, the *weighted white count of the fresh atom* is the
weighted white count of `β` read from the landing point `(j(e) + r, l(e) + ℓ)` of the first
passage:
```
N^e_p(a) = N^*((j(e) + r, l(e) + ℓ), β; p).
```
It is the count along the fresh path `y^e(a)`, whose fresh law is `μ_{e,g}`.

## Main definitions

* `CollatzPosDens.trWhiteCount n ξ e a p`: the weighted white count `N^e_p(a) ∈ ℝ`.

## Main results

* `CollatzPosDens.trWhiteCount_mk`:
  `N^e_p(((r, ℓ), β)) = N^*((j(e) + r, l(e) + ℓ), β; p)`.
* `CollatzPosDens.trWhiteCount_zero`: `N^e_0(a) = 0`.
* `CollatzPosDens.trWhiteCount_nonneg`, `CollatzPosDens.trWhiteCount_mono`: the count
  is nonnegative and nondecreasing in `p`.
* `CollatzPosDens.trWhiteCount_of_le`: for `a ∈ 𝒜_n`, `N^e_p(a) = N^e_{⌊n/2⌋}(a)` for
  `p ≥ ⌊n/2⌋`.

## Implementation notes

The definition is stated for every `n`, every `e ∈ ℤ × ℤ` and every `a` in the ambient type
`(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n`; the hypotheses `n ≥ 1`, `e ∈ 𝒫` and `a ∈ 𝒜_n`
play no role in the definition and are used only in the lemmas that need them. The residue
`ξ ∈ G_n`, on which `N^*` depends through whiteness, is an explicit argument.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- The weighted white count `N^e_p(a) = N^*((j(e) + r, l(e) + ℓ), β; p)` of the fresh atom
`a = ((r, ℓ), β)` from the entry point `e` up to time `p`, whiteness referring to `(n, ξ, ε_*)`. -/
@[collatz_pos_dens "def_tr_white_count"]
noncomputable def trWhiteCount (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ)
    (a : (ℕ × ℤ) × List (List ℤ × ℤ)) (p : ℕ) : ℝ :=
  trCount n ξ (bkJ e + a.1.1, bkL e + a.1.2) a.2 p

variable {n : ℕ} {ξ : ResidueGroup n}

/-- Unfolding lemma for `trWhiteCount`. -/
lemma trWhiteCount_def (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) (p : ℕ) :
    trWhiteCount n ξ e a p = trCount n ξ (bkJ e + a.1.1, bkL e + a.1.2) a.2 p :=
  rfl

/-- For the atom `((r, ℓ), β)`, `N^e_p = N^*((j(e) + r, l(e) + ℓ), β; p)`. -/
@[simp]
lemma trWhiteCount_mk (e : ℤ × ℤ) (r : ℕ) (ℓ : ℤ) (β : List (List ℤ × ℤ)) (p : ℕ) :
    trWhiteCount n ξ e ((r, ℓ), β) p = trCount n ξ (bkJ e + r, bkL e + ℓ) β p :=
  rfl

/-- `N^e_0(a) = 0`. -/
@[simp]
lemma trWhiteCount_zero (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    trWhiteCount n ξ e a 0 = 0 :=
  trCount_zero _ _

/-- The weighted white count of a fresh atom is nonnegative. -/
lemma trWhiteCount_nonneg (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) (p : ℕ) :
    0 ≤ trWhiteCount n ξ e a p :=
  trCount_nonneg _ _ _

/-- The weighted white count of a fresh atom is nondecreasing in time. -/
lemma trWhiteCount_mono (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    Monotone (trWhiteCount n ξ e a) :=
  trCount_mono _ _

/-- For a fresh atom `a ∈ 𝒜_n`, the count is constant from time `⌊n/2⌋` on. -/
lemma trWhiteCount_of_le (e : ℤ × ℤ) {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n)
    {p : ℕ} (hp : n / 2 ≤ p) : trWhiteCount n ξ e a p = trWhiteCount n ξ e a (n / 2) := by
  unfold trWhiteCount
  rw [← trAtoms_length ha] at hp ⊢
  exact trCount_of_length_le _ _ hp

end CollatzPosDens
