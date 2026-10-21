/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05OfflawContrib
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Fin.Basic

/-!
# Offset-law certificates

A table `g = (g_0, …, g_6198)` of natural numbers, read as the step function `2^{-62} g_{ix(y)}`
on the offset grid `(ξ_k)`, is an *offset-law certificate* if

1. `g_0 ≤ g_1 ≤ ⋯ ≤ g_6198 ≤ ⌊2^62 𝖦₀(ξ_6198)⌋`; and
2. for every `0 ≤ k ≤ 6198`,
   `g_k ≤ max(⌊2^62 𝖦₀(ξ_k)⌋, ∑_{a=1}^{60} c_g(k,a))`.

Here `𝖦₀` is the tail floor `CollatzPosDens.offlawFloor` and `c_g(k,a)` the integer contribution
`CollatzPosDens.offlawContrib`. Condition (2) says that the table is a sub-fixed point of the
one-letter recursion of the offset law, up to the tail floor.

## Main definitions

* `CollatzPosDens.IsOfflawCert g`: `g : Fin 6199 → ℕ` is an offset-law certificate.

## Main results

* `CollatzPosDens.isOfflawCert_iff`: the two conditions in natural-number arithmetic, with
  monotonicity checked on consecutive indices.

## Implementation notes

The predicate is stated with the real tail floor `⌊2^62 𝖦₀(ξ_k)⌋₊` and the real grid point
`ξ_k ∈ ℚ ⊆ ℝ`. `CollatzPosDens.isOfflawCert_iff` rewrites each floor as the
natural-number quotient `2^62 (n_k - 2560)/(n_k + 1024)` with `n_k = 512 ξ_k`, so every
condition becomes a closed statement about natural numbers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- **Offset-law certificate**: a table `g = (g_0, …, g_6198)` with
(i) `g` nondecreasing and `g_6198 ≤ ⌊2^62 𝖦₀(ξ_6198)⌋`; and
(ii) `g_k ≤ max(⌊2^62 𝖦₀(ξ_k)⌋, ∑_{a=1}^{60} c_g(k,a))` for every `0 ≤ k ≤ 6198`. -/
@[collatz_pos_dens "def_s05_offlaw_cert"]
structure IsOfflawCert (g : Fin 6199 → ℕ) : Prop where
  /-- Condition (i), first half: `g_0 ≤ g_1 ≤ ⋯ ≤ g_6198`. -/
  monotone : Monotone g
  /-- Condition (i), second half: `g_6198 ≤ ⌊2^62 𝖦₀(ξ_6198)⌋`. -/
  le_floor_last : g 6198 ≤ ⌊(2 : ℝ) ^ 62 * offlawFloor ((offlawGrid 6198 : ℚ) : ℝ)⌋₊
  /-- Condition (ii): `g_k ≤ max(⌊2^62 𝖦₀(ξ_k)⌋, ∑_{a=1}^{60} c_g(k,a))`. -/
  le_max : ∀ k : Fin 6199, g k ≤
    max ⌊(2 : ℝ) ^ 62 * offlawFloor ((offlawGrid k : ℚ) : ℝ)⌋₊
      (∑ a ∈ Icc 1 60, offlawContrib g k a)

/-- An offset-law certificate in natural-number arithmetic: monotonicity on consecutive
indices, and each floor `⌊2^62 𝖦₀(ξ_k)⌋` as the quotient `offlawFloorNum 62 n_k 512`. -/
theorem isOfflawCert_iff (g : Fin 6199 → ℕ) :
    IsOfflawCert g ↔
      (∀ k : Fin 6198, g k.castSucc ≤ g k.succ) ∧
      g 6198 ≤ offlawFloorNum 62 (offlawGridNum 6198) 512 ∧
      (∀ k : Fin 6199, g k ≤ max (offlawFloorNum 62 (offlawGridNum k) 512)
        (∑ a ∈ Icc 1 60, offlawContrib g k a)) := by
  simp only [← floor_two_pow_mul_offlawFloor_offlawGrid, ← Fin.monotone_iff_le_succ]
  exact ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Being an offset-law certificate is decidable, via `CollatzPosDens.isOfflawCert_iff`. -/
instance (g : Fin 6199 → ℕ) : Decidable (IsOfflawCert g) :=
  decidable_of_iff _ (isOfflawCert_iff g).symm

end CollatzPosDens
