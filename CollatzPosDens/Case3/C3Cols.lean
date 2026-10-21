/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Case3.C3Anchors
public import CollatzPosDens.Transfer.S02Wtot
public import CollatzPosDens.Transfer.S02Xd
public import CollatzPosDens.Transfer.S02Xl
public import CollatzPosDens.Transfer.S02Xo

/-!
# Anchor columns

For a Fourier index `ι ∈ 𝔍`, a point `e ∈ 𝒫`, a triangle `Δ₀ ∈ 𝔗`, a horizon `v ∈ ℕ` and a real
threshold `s`, the *anchor columns* are the set of integers
$$\mathcal U_{e,\Delta_0,v,s}(\iota) :=
  \{z - j(e) + i : z \in \mathrm{Anc}(\Delta_0, s, W(\iota,v)),\
  i \in \mathbb Z,\ -X_d(\iota,v) - \tfrac14 X_l(\iota,v) < i
  < \lambda X_o(\iota) + \lambda_0 X_l(\iota,v) + X_d(\iota,v)\},$$
where `λ = log 2 / log 9` is the slope, `λ₀ = λ - 1/4` the drift, `X_o(ι)` the overshoot allowance,
`X_l(ι, v)` the list allowance, `X_d(ι, v)` the drift-free allowance and
`W(ι, v) = X_o(ι) + X_l(ι, v)` the total allowance. It is the union over the integers `i` of
that open interval of the translates `Anc(Δ₀, s, W(ι, v)) - j(e) + i` of the anchor set.

## Main definitions

* `CollatzPosDens.c3AnchorCols ι T e Δ₀ v s`: the anchor columns relative to a family `T` of
  triangles; for the canonical family take `T = bkFamily n ξ ε`.

## Main results

* `CollatzPosDens.mem_c3AnchorCols`: membership in the anchor columns.
* `CollatzPosDens.c3AnchorCols_eq_iUnion`: the anchor columns are the union of the translates
  of the anchor set over the integers of the window.
* `CollatzPosDens.sub_mem_c3AnchorCols`: `z - j(e)` lies in the anchor columns for every
  anchor `z`.
* `CollatzPosDens.c3AnchorCols_mono_family`, `CollatzPosDens.c3AnchorCols_antitone_size`:
  monotonicity in the family and the threshold.

## Implementation notes

The anchor columns are usually considered for the canonical family `𝔗 = 𝔗_{n,ξ,ε}`, with `e`
a point of `𝒫` and `Δ₀ ∈ 𝔗`. The definition is stated for an arbitrary family `T`, any
`e ∈ ℤ × ℤ` and any triangle `Δ₀`; none of these restrictions is needed to form the set. The
window bounds are compared in `ℝ`; the allowances `X_d(ι, v)`, `X_l(ι, v)` and `W(ι, v)` are
rational and enter through their casts.
-/

@[expose] public section

namespace CollatzPosDens

variable {ι : FIndex} {T T' : Set BkTriangle} {e : ℤ × ℤ} {Δ₀ : BkTriangle} {v : ℕ}
  {s s' : ℝ} {r : ℤ}

/-- The anchor columns `𝒰_{e,Δ₀,v,s}(ι)`: the integers `z - j(e) + i` with
`z ∈ Anc(Δ₀, s, W(ι, v))` and `i ∈ ℤ` with
`-X_d(ι, v) - X_l(ι, v)/4 < i < λ X_o(ι) + λ₀ X_l(ι, v) + X_d(ι, v)`. -/
@[collatz_pos_dens "def_c3_cols"]
def c3AnchorCols (ι : FIndex) (T : Set BkTriangle) (e : ℤ × ℤ) (Δ₀ : BkTriangle) (v : ℕ)
    (s : ℝ) : Set ℤ :=
  {r | ∃ z ∈ bkAnchors T Δ₀ s (totalAllowance ι v), ∃ i : ℤ,
    -(Xd ι v : ℝ) - (Xl ι v : ℝ) / 4 < i ∧
      (i : ℝ) < alpha * overshootAllowance ι + drift * Xl ι v + Xd ι v ∧ r = z - bkJ e + i}

/-- Membership in the anchor columns. -/
theorem mem_c3AnchorCols :
    r ∈ c3AnchorCols ι T e Δ₀ v s ↔
      ∃ z ∈ bkAnchors T Δ₀ s (totalAllowance ι v), ∃ i : ℤ,
        -(Xd ι v : ℝ) - (Xl ι v : ℝ) / 4 < i ∧
          (i : ℝ) < alpha * overshootAllowance ι + drift * Xl ι v + Xd ι v ∧ r = z - bkJ e + i :=
  Iff.rfl

/-- The anchor columns are the union, over the integers `i` of the window, of the translates
`Anc(Δ₀, s, W(ι, v)) - j(e) + i` of the anchor set. -/
theorem c3AnchorCols_eq_iUnion :
    c3AnchorCols ι T e Δ₀ v s =
      ⋃ i ∈ {i : ℤ | -(Xd ι v : ℝ) - (Xl ι v : ℝ) / 4 < i ∧
          (i : ℝ) < alpha * overshootAllowance ι + drift * Xl ι v + Xd ι v},
        (fun z ↦ z - bkJ e + i) '' bkAnchors T Δ₀ s (totalAllowance ι v) := by
  ext r
  simp only [mem_c3AnchorCols, Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨z, hz, i, h₁, h₂, rfl⟩
    exact ⟨i, ⟨h₁, h₂⟩, z, hz, rfl⟩
  · rintro ⟨i, ⟨h₁, h₂⟩, z, hz, rfl⟩
    exact ⟨z, hz, i, h₁, h₂, rfl⟩

/-- The window of the anchor columns contains `0`. -/
theorem zero_mem_c3AnchorCols_window :
    -(Xd ι v : ℝ) - (Xl ι v : ℝ) / 4 < 0 ∧
      (0 : ℝ) < alpha * overshootAllowance ι + drift * Xl ι v + Xd ι v := by
  have hd : (0 : ℝ) < Xd ι v := by exact_mod_cast Xd_pos ι v
  have hl : (0 : ℝ) ≤ Xl ι v := by exact_mod_cast (Xl_pos ι v).le
  have ho : (0 : ℝ) ≤ overshootAllowance ι := Nat.cast_nonneg _
  have := mul_nonneg alpha_pos.le ho
  have := mul_nonneg drift_pos.le hl
  constructor <;> linarith

/-- For every anchor `z ∈ Anc(Δ₀, s, W(ι, v))`, `z - j(e)` lies in the anchor columns. -/
theorem sub_mem_c3AnchorCols {z : ℤ} (hz : z ∈ bkAnchors T Δ₀ s (totalAllowance ι v)) :
    z - bkJ e ∈ c3AnchorCols ι T e Δ₀ v s :=
  ⟨z, hz, 0, by exact_mod_cast zero_mem_c3AnchorCols_window.1,
    by exact_mod_cast zero_mem_c3AnchorCols_window.2, by ring⟩

/-- The anchor columns are monotone in the family. -/
theorem c3AnchorCols_mono_family (h : T ⊆ T') :
    c3AnchorCols ι T e Δ₀ v s ⊆ c3AnchorCols ι T' e Δ₀ v s :=
  fun _ ⟨z, hz, i, h₁, h₂, hr⟩ => ⟨z, bkAnchors_mono_family h hz, i, h₁, h₂, hr⟩

/-- The anchor columns shrink as the size threshold grows. -/
theorem c3AnchorCols_antitone_size (h : s ≤ s') :
    c3AnchorCols ι T e Δ₀ v s' ⊆ c3AnchorCols ι T e Δ₀ v s :=
  fun _ ⟨z, hz, i, h₁, h₂, hr⟩ => ⟨z, bkAnchors_antitone_size h hz, i, h₁, h₂, hr⟩

end CollatzPosDens
