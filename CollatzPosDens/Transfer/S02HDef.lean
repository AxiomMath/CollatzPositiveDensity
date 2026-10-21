/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Beta
public import CollatzPosDens.Transfer.S02H
public import CollatzPosDens.Transfer.S02Schedule
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Positivity

/-!
# The window length `h_*`

For a Fourier index `ι` and `u ∈ ℕ` the window length is the natural number
`h_*(ι, u) := ⌈α_sc(ι) β_*(ι, u)⌉ + H_*(ι)`, where `α_sc(ι)` is the slope of the trace schedule
(`α_sc(o) = 113/1000`, `α_sc(b) = 3/25`), `β_*` is the oversize threshold and `H_*(ι)` is the
window height (`H_*(o) = 10100`, `H_*(b) = 500`). Below `ι` is fixed and suppressed. Writing
`α_sc = a / d` with `a, d ∈ ℕ`, and since `β_*(u)` is a natural number, the ceiling is the ceiling
division `(a β_*(u) + d - 1) / d` of `ℕ`. As `β_*` is monotone, `h_*` is monotone, and
`h_*(u) ≥ H_*` always.

## Main definitions

* `CollatzPosDens.windowLength`: the window length `h_*(ι, u)`.

## Main results

* `CollatzPosDens.windowLength_eq_div`: `h_*(u) = (a β_*(u) + d - 1) / d + H_*`, `α_sc = a / d`.
* `CollatzPosDens.windowLength_o_eq_div`, `CollatzPosDens.windowLength_b_eq_div`: the same with
  the constants evaluated, `h_*(o, u) = (113 β_*(o, u) + 999) / 1000 + 10100` and
  `h_*(b, u) = (3 β_*(b, u) + 24) / 25 + 500`.
* `CollatzPosDens.windowLength_monotone`: `h_*` is monotone.
* `CollatzPosDens.le_windowLength`: `H_* ≤ h_*(u)`.
* `CollatzPosDens.windowLength_mul_ge`: `a β_*(u) + d H_* ≤ d h_*(u)`.
* `CollatzPosDens.windowLength_mul_le`: `d h_*(u) ≤ a β_*(u) + d - 1 + d H_*`.

## Implementation notes

The ceiling is taken in `ℝ` with `Nat.ceil`; `windowLength_eq_div` converts it to natural-number
arithmetic, with `a = traceSlopeNum ι` and `d = traceSlopeDen ι`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The window length `h_*(ι, u) := ⌈α_sc(ι) β_*(ι, u)⌉ + H_*(ι) ∈ ℕ`, where `α_sc(ι)` is the
slope of the trace schedule. -/
@[collatz_pos_dens "def_s02_h"]
noncomputable def windowLength (ι : FIndex) (u : ℕ) : ℕ :=
  ⌈(traceSlope ι : ℝ) * betaStar ι u⌉₊ + Hstar ι

/-- The window length is `h_*(ι, u) = ⌈α_sc(ι) β_*(ι, u)⌉ + H_*(ι)`. -/
theorem windowLength_def (ι : FIndex) (u : ℕ) :
    windowLength ι u = ⌈(traceSlope ι : ℝ) * betaStar ι u⌉₊ + Hstar ι := rfl

/-- The ceiling of a quotient of natural numbers in `ℝ` is a natural-number division. -/
private lemma windowLength_natCeil_div (a : ℕ) {d : ℕ} (hd : 0 < d) :
    ⌈(a : ℝ) / d⌉₊ = (a + d - 1) / d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hdr]
    have : a ≤ (a + d - 1) / d * d := by
      have h1 := Nat.div_add_mod (a + d - 1) d
      have h2 := Nat.mod_lt (a + d - 1) hd
      rw [Nat.mul_comm] at h1
      omega
    exact_mod_cast this
  · rw [Nat.div_le_iff_le_mul_add_pred hd]
    have h := Nat.le_ceil ((a : ℝ) / d)
    rw [div_le_iff₀ hdr] at h
    have : a ≤ ⌈(a : ℝ) / d⌉₊ * d := by exact_mod_cast h
    rw [Nat.mul_comm] at this
    omega

/-- The ceiling in `h_*` is the ceiling division of natural numbers: writing
`α_sc(ι) = a / d`, `h_*(ι, u) = (a β_*(ι, u) + d - 1) / d + H_*(ι)`. -/
theorem windowLength_eq_div (ι : FIndex) (u : ℕ) :
    windowLength ι u =
      (traceSlopeNum ι * betaStar ι u + traceSlopeDen ι - 1) / traceSlopeDen ι + Hstar ι := by
  rw [windowLength_def, ← windowLength_natCeil_div _ (traceSlopeDen_pos ι), traceSlope_eq_div]
  push_cast
  rw [div_mul_eq_mul_div]

/-- The window length at the original index:
`h_*(o, u) = (113 β_*(o, u) + 999) / 1000 + 10100`. -/
theorem windowLength_o_eq_div (u : ℕ) :
    windowLength .o u = (113 * betaStar .o u + 999) / 1000 + 10100 := by
  rw [windowLength_eq_div, traceSlopeNum_o, traceSlopeDen_o, Hstar_o]
  omega

/-- The window length at the bootstrap index:
`h_*(b, u) = (3 β_*(b, u) + 24) / 25 + 500`. -/
theorem windowLength_b_eq_div (u : ℕ) :
    windowLength .b u = (3 * betaStar .b u + 24) / 25 + 500 := by
  rw [windowLength_eq_div, traceSlopeNum_b, traceSlopeDen_b, Hstar_b]
  omega

/-- The window length satisfies `H_*(ι) ≤ h_*(ι, u)`. -/
theorem le_windowLength (ι : FIndex) (u : ℕ) : Hstar ι ≤ windowLength ι u := by
  rw [windowLength_def]
  omega

/-- The window length `h_*(ι, u)` is positive. -/
theorem windowLength_pos (ι : FIndex) (u : ℕ) : 0 < windowLength ι u :=
  lt_of_lt_of_le (Hstar_pos ι) (le_windowLength ι u)

/-- Writing `α_sc(ι) = a / d`, the window length satisfies
`a β_*(ι, u) + d H_*(ι) ≤ d h_*(ι, u)`. -/
theorem windowLength_mul_ge (ι : FIndex) (u : ℕ) :
    traceSlopeNum ι * betaStar ι u + traceSlopeDen ι * Hstar ι ≤
      traceSlopeDen ι * windowLength ι u := by
  rw [windowLength_eq_div]
  cases ι <;> simp only [traceSlopeNum_o, traceSlopeDen_o, traceSlopeNum_b, traceSlopeDen_b]
    <;> omega

/-- Writing `α_sc(ι) = a / d`, the window length satisfies
`d h_*(ι, u) ≤ a β_*(ι, u) + d - 1 + d H_*(ι)`. -/
theorem windowLength_mul_le (ι : FIndex) (u : ℕ) :
    traceSlopeDen ι * windowLength ι u ≤
      traceSlopeNum ι * betaStar ι u + traceSlopeDen ι - 1 + traceSlopeDen ι * Hstar ι := by
  rw [windowLength_eq_div]
  cases ι <;> simp only [traceSlopeNum_o, traceSlopeDen_o, traceSlopeNum_b, traceSlopeDen_b]
    <;> omega

/-- The window length `h_*(ι, ·)` is monotone. -/
theorem windowLength_monotone (ι : FIndex) : Monotone (windowLength ι) := by
  intro p q hpq
  rw [windowLength_eq_div, windowLength_eq_div]
  have := betaStar_monotone ι hpq
  have := Nat.mul_le_mul_left (traceSlopeNum ι) this
  have := Nat.div_le_div_right (c := traceSlopeDen ι)
    (Nat.sub_le_sub_right (Nat.add_le_add_right this (traceSlopeDen ι)) 1)
  omega

end CollatzPosDens
