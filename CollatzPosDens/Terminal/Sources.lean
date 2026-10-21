/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# The source set `𝒮_{j,X}(t)`

For `j ≥ 0`, a real `X` and a starting point `t`, the source set
$$\mathcal S_{j,X}(t) = \{\mathrm{src}(w, R_h) : (h, w) \text{ a counted pair of }
  \Upsilon_{j,X}(t)\} \subseteq \mathbb Z$$
collects the sources of the counted pairs of the unweighted terminal mass, where `R_h` is the
endpoint of the history `h`. Each counted word `w` is admissible from `R_h`, so its source is
an integer.

## Main definitions

* `CollatzPosDens.sources j X t`: the source set `𝒮_{j,X}(t) ⊆ ℤ`.

## Main results

* `CollatzPosDens.mem_sources`: membership in `𝒮_{j,X}(t)`.
* `CollatzPosDens.image_intCast_sources`: the image of `𝒮_{j,X}(t)` in `ℚ` is the image of
  the counted pairs under `(h, w) ↦ src(w, R_h)`.
* `CollatzPosDens.sources_finite`: `𝒮_{j,X}(t)` is finite.

## Implementation notes

The source map takes values in `ℚ`. The set is defined as the integers `z` whose image in `ℚ`
is a source of a counted pair; since every counted word is admissible, every such source is the
image of an integer, so this loses nothing (`CollatzPosDens.image_intCast_sources`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {j : ℕ} {X : ℝ} {t : ℚ}

/-- The source set `𝒮_{j,X}(t) = {src(w, R_h) : (h, w) a counted pair of Υ_{j,X}(t)} ⊆ ℤ`. -/
@[collatz_pos_dens "def_sources"]
def sources (j : ℕ) (X : ℝ) (t : ℚ) : Set ℤ :=
  {z | ∃ p ∈ unweightedMassPairs j X t, src p.2 (historyEndpoint t p.1) = z}

/-- Membership in the source set `𝒮_{j,X}(t)`. -/
theorem mem_sources {z : ℤ} :
    z ∈ sources j X t ↔
      ∃ p ∈ unweightedMassPairs j X t, src p.2 (historyEndpoint t p.1) = z :=
  Iff.rfl

/-- The source of a counted pair is an integer. -/
theorem exists_intCast_src_of_mem_unweightedMassPairs {p : (Fin j → Word) × Word}
    (hp : p ∈ unweightedMassPairs j X t) :
    ∃ z : ℤ, src p.2 (historyEndpoint t p.1) = z :=
  ⟨_, (Rat.coe_int_num_of_den_eq_one hp.2.2.2.den_src_eq_one).symm⟩

/-- The source of a counted pair lies in the source set. -/
theorem src_mem_sources {p : (Fin j → Word) × Word}
    (hp : p ∈ unweightedMassPairs j X t) {z : ℤ} (hz : src p.2 (historyEndpoint t p.1) = z) :
    z ∈ sources j X t :=
  ⟨p, hp, hz⟩

/-- The image of `𝒮_{j,X}(t)` in `ℚ` is the set of sources `src(w, R_h)` of the counted pairs
`(h, w)` of `Υ_{j,X}(t)`. -/
theorem image_intCast_sources (j : ℕ) (X : ℝ) (t : ℚ) :
    ((↑) : ℤ → ℚ) '' sources j X t =
      (fun p => src p.2 (historyEndpoint t p.1)) '' unweightedMassPairs j X t := by
  ext q
  constructor
  · rintro ⟨z, ⟨p, hp, hz⟩, rfl⟩
    exact ⟨p, hp, hz⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨z, hz⟩ := exists_intCast_src_of_mem_unweightedMassPairs hp
    exact ⟨z, ⟨p, hp, hz⟩, hz.symm⟩

/-- The source set `𝒮_{j,X}(t)` is finite. -/
theorem sources_finite (j : ℕ) (X : ℝ) (t : ℚ) : (sources j X t).Finite := by
  refine Set.Finite.of_finite_image ?_ (Int.cast_injective (α := ℚ)).injOn
  rw [image_intCast_sources]
  exact (unweightedMassPairs_finite j X t).image _

end CollatzPosDens
