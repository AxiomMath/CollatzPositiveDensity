/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrAtoms
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# The fresh path from an entry point

For an entry point `e ∈ 𝒫` and a fresh atom `a = ((r, ℓ), β) ∈ 𝒜_n`, the fresh path starts at
the landing point `(j(e) + r, l(e) + ℓ)` and then reads the blocks of `β`: its `p`-th point is
`y^e_p(a) = x_p((j(e) + r, l(e) + ℓ), β)`, where `x_p` is `trPath`, and
`y^e(a) = (y^e_p(a))_{p ∈ ℕ}`.

## Main definitions

* `CollatzPosDens.trFreshPath`: the point `y^e_p(a)`; its curried form `trFreshPath e a` is
  the whole sequence `y^e(a)`.

## Main results

* `CollatzPosDens.trFreshPath_def`: `y^e_p(((r, ℓ), β)) = x_p((j(e) + r, l(e) + ℓ), β)`.
* `CollatzPosDens.trFreshPath_zero`: `y^e_0(a) = (j(e) + r, l(e) + ℓ)`.
* `CollatzPosDens.trFreshPath_of_le`: for `a ∈ 𝒜_n` the fresh path is constant from time
  `⌊n/2⌋` on.
* `CollatzPosDens.trFreshPath_mem_bkPoints`: for `e ∈ 𝒫` the fresh path stays in `𝒫`.

## Implementation notes

The definition does not depend on `n`, on `n ≥ 1`, on `e ∈ 𝒫`, nor on the membership
`a ∈ 𝒜_n`: it is stated for every `e ∈ ℤ × ℤ` and every `a ∈ (ℕ × ℤ) × List (List ℤ × ℤ)`, the
ambient type of `𝒜_n`. Restricted to `e ∈ 𝒫` and `a ∈ 𝒜_n` it is the fresh path `y^e_p(a)`;
the hypotheses appear only in the lemmas that need them.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The fresh path `y^e_p(a) = x_p((j(e) + r, l(e) + ℓ), β)` of the atom `a = ((r, ℓ), β)` from
the entry point `e`, at time `p`. -/
@[collatz_pos_dens "def_tr_fresh_path"]
def trFreshPath (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) (p : ℕ) : ℤ × ℤ :=
  trPath (bkJ e + a.1.1, bkL e + a.1.2) a.2 p

/-- For the atom `((r, ℓ), β)`, `y^e_p = x_p((j(e) + r, l(e) + ℓ), β)`. -/
theorem trFreshPath_def (e : ℤ × ℤ) (r : ℕ) (ℓ : ℤ) (β : List (List ℤ × ℤ)) (p : ℕ) :
    trFreshPath e ((r, ℓ), β) p = trPath (bkJ e + r, bkL e + ℓ) β p :=
  rfl

/-- The fresh path starts at the landing point `(j(e) + r, l(e) + ℓ)`. -/
@[simp]
theorem trFreshPath_zero (e : ℤ × ℤ) (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    trFreshPath e a 0 = (bkJ e + a.1.1, bkL e + a.1.2) := by
  simp [trFreshPath]

/-- For a fresh atom `a ∈ 𝒜_n`, the fresh path is constant from time `⌊n/2⌋` on. -/
theorem trFreshPath_of_le {n : ℕ} (e : ℤ × ℤ) {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ trAtoms n) {p : ℕ} (hp : n / 2 ≤ p) :
    trFreshPath e a p = trFreshPath e a (n / 2) := by
  unfold trFreshPath
  rw [← trAtoms_length ha] at hp ⊢
  exact trPath_of_length_le _ _ hp

/-- From an entry point in `𝒫`, the fresh path stays in `𝒫`. -/
theorem trFreshPath_mem_bkPoints {e : ℤ × ℤ} (he : e ∈ bkPoints)
    (a : (ℕ × ℤ) × List (List ℤ × ℤ)) (p : ℕ) : trFreshPath e a p ∈ bkPoints := by
  refine trPath_mem_bkPoints ?_ _ _
  rw [mem_bkPoints_mk]
  have := mem_bkPoints.1 he
  omega

end CollatzPosDens
