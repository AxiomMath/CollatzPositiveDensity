/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.Case3.C3Tip

/-!
# Anchor sets

For a family `T` of triangles, a triangle `Δ₀`, a size threshold `s` and a height window
`b`, the *anchor set* `Anc(Δ₀, s, b) ⊆ ℤ` is the set of first corner coordinates `j_Δ` of
the triangles `Δ ∈ T` with `s_Δ ≥ s` whose tip lies in the window
`l_{Δ₀} ≤ tip(Δ) ≤ l_{Δ₀} + b`.

## Main definitions

* `CollatzPosDens.bkAnchors T Δ₀ s b`: the anchor set of `Δ₀` relative to a family `T` of
  triangles; for the canonical family take `T = bkFamily n ξ ε`.

## Main results

* `CollatzPosDens.mem_bkAnchors`: membership in the anchor set.
* `CollatzPosDens.j_mem_bkAnchors`: the anchor of a qualifying triangle is an anchor.
* `CollatzPosDens.bkAnchors_mono_family`, `CollatzPosDens.bkAnchors_antitone_size`,
  `CollatzPosDens.bkAnchors_mono_window`: monotonicity in the family, the threshold and
  the window.
* `CollatzPosDens.bkAnchors_eq_empty_of_neg`: the anchor set is empty for `b < 0`.

## Implementation notes

The anchor set is usually considered for the canonical family `𝔗 = 𝔗_{n,ξ,ε}`, with
`Δ₀ ∈ 𝔗` and `b ≥ 0`. The definition is stated for an arbitrary family `T` of triangles, any
triangle `Δ₀` and all real `s, b`; none of these restrictions is needed to form the set, and
for `b < 0` the set is empty.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open BkTriangle

variable {T T' : Set BkTriangle} {Δ₀ : BkTriangle} {s s' b b' : ℝ} {z : ℤ}

/-- The anchor set `Anc(Δ₀, s, b)`: the integers `j_Δ` for `Δ ∈ T` with `s_Δ ≥ s` and
`l_{Δ₀} ≤ tip(Δ) ≤ l_{Δ₀} + b`. -/
@[collatz_pos_dens "def_c3_anchors"]
def bkAnchors (T : Set BkTriangle) (Δ₀ : BkTriangle) (s b : ℝ) : Set ℤ :=
  BkTriangle.j '' {Δ | Δ ∈ T ∧ s ≤ Δ.s ∧ (Δ₀.l : ℝ) ≤ Δ.tip ∧ Δ.tip ≤ Δ₀.l + b}

/-- Membership in the anchor set. -/
@[simp]
theorem mem_bkAnchors :
    z ∈ bkAnchors T Δ₀ s b ↔
      ∃ Δ ∈ T, s ≤ Δ.s ∧ (Δ₀.l : ℝ) ≤ Δ.tip ∧ Δ.tip ≤ Δ₀.l + b ∧ Δ.j = z := by
  constructor
  · rintro ⟨Δ, ⟨hΔ, hs, h₁, h₂⟩, rfl⟩
    exact ⟨Δ, hΔ, hs, h₁, h₂, rfl⟩
  · rintro ⟨Δ, hΔ, hs, h₁, h₂, rfl⟩
    exact ⟨Δ, ⟨hΔ, hs, h₁, h₂⟩, rfl⟩

/-- The anchor of a qualifying triangle lies in the anchor set. -/
theorem j_mem_bkAnchors {Δ : BkTriangle} (hΔ : Δ ∈ T) (hs : s ≤ Δ.s)
    (h₁ : (Δ₀.l : ℝ) ≤ Δ.tip) (h₂ : Δ.tip ≤ Δ₀.l + b) : Δ.j ∈ bkAnchors T Δ₀ s b :=
  ⟨Δ, ⟨hΔ, hs, h₁, h₂⟩, rfl⟩

/-- Every anchor is at least `1`. -/
theorem one_le_of_mem_bkAnchors (hz : z ∈ bkAnchors T Δ₀ s b) : 1 ≤ z := by
  obtain ⟨Δ, -, rfl⟩ := hz
  exact Δ.one_le_j

/-- The anchor set is monotone in the family. -/
theorem bkAnchors_mono_family (h : T ⊆ T') : bkAnchors T Δ₀ s b ⊆ bkAnchors T' Δ₀ s b :=
  Set.image_mono fun _ ⟨hΔ, hs, h₁, h₂⟩ => ⟨h hΔ, hs, h₁, h₂⟩

/-- The anchor set shrinks as the size threshold grows. -/
theorem bkAnchors_antitone_size (h : s ≤ s') : bkAnchors T Δ₀ s' b ⊆ bkAnchors T Δ₀ s b :=
  Set.image_mono fun _ ⟨hΔ, hs, h₁, h₂⟩ => ⟨hΔ, h.trans hs, h₁, h₂⟩

/-- The anchor set grows with the window. -/
theorem bkAnchors_mono_window (h : b ≤ b') : bkAnchors T Δ₀ s b ⊆ bkAnchors T Δ₀ s b' :=
  Set.image_mono fun _ ⟨hΔ, hs, h₁, h₂⟩ => ⟨hΔ, hs, h₁, h₂.trans (by linarith)⟩

/-- For a negative window the anchor set is empty. -/
theorem bkAnchors_eq_empty_of_neg (hb : b < 0) : bkAnchors T Δ₀ s b = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨Δ, ⟨-, -, h₁, h₂⟩, -⟩
  linarith

end CollatzPosDens
