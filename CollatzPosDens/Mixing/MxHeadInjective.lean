/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.DyadicReduction
public import CollatzPosDens.Transfer.ResidueMap
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxClearedBound
public import CollatzPosDens.Mixing.MxOffsetInjective

/-!
# Heads are separated modulo `3 ^ n`

Let `k, l ∈ ℕ` and let `h, h'` be words in the head gate `CollatzPosDens.mxHeadGate n k l`
whose offsets `CollatzPosDens.off` have the same image under the reduction
`CollatzPosDens.dyadicRed n` modulo `3 ^ n`. Then `h = h'`.

Since the valuation sum of `h` is `l`, the cleared offset `N = 2 ^ l off(h)` is a natural
number, and likewise `N' = 2 ^ l off(h')`. Reduction modulo `3 ^ n` is a ring homomorphism on
`ℤ[1/2]`, so `N ≡ N' (mod 3 ^ n)`. Both are below `3 ^ n` by
`CollatzPosDens.two_pow_mul_off_lt_three_pow_of_mem_mxHeadGate`, hence `N = N'` and
`off(h) = off(h')`. As both words have length `k + 1`,
`CollatzPosDens.off_injective_of_length_eq` gives `h = h'`.

## Main results

* `CollatzPosDens.eq_of_dyadicRed_off_eq_of_mem_mxHeadGate`: two words in the same head gate
  with the same offset modulo `3 ^ n` are equal.

## Implementation notes

The statement holds for every natural number `n`, including `n = 0`, so it carries no
hypothesis `n ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Two words in the head gate `mxHeadGate n k l` whose offsets have the same reduction modulo
`3 ^ n` are equal. -/
@[collatz_pos_dens "lem_mx_head_injective"]
theorem eq_of_dyadicRed_off_eq_of_mem_mxHeadGate {n k l : ℕ} {h h' : Word}
    (hh : h ∈ mxHeadGate n k l) (hh' : h' ∈ mxHeadGate n k l)
    (hred : dyadicRed n ⟨off h, off_mem_dyadicRationals h⟩ =
      dyadicRed n ⟨off h', off_mem_dyadicRationals h'⟩) :
    h = h' := by
  have key : ∀ w ∈ mxHeadGate n k l, ∃ N : ℕ, off w * 2 ^ l = N ∧ N < 3 ^ n ∧
      (N : ResidueGroup n) = dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ * 2 ^ l := by
    intro w hw
    have hlen := length_of_mem_mxHeadGate hw
    have hA := valSum_of_mem_mxHeadGate hw
    have hne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨N, -, hN⟩ := exists_odd_off_mul_two_pow_valSum hne
    rw [hA] at hN
    refine ⟨N, hN, ?_, ?_⟩
    · have hb := two_pow_mul_off_lt_three_pow_of_mem_mxHeadGate hw
      rw [mul_comm, hN] at hb
      exact_mod_cast hb
    · have he : (⟨off w, off_mem_dyadicRationals w⟩ : dyadicRationals) * 2 ^ l =
          ((N : ℤ) : dyadicRationals) :=
        Subtype.ext (by
          have h2 : ((2 : dyadicRationals) : ℚ) = 2 := rfl
          simpa [h2] using hN)
      have := congrArg (dyadicRed n) he
      rw [map_mul, map_pow, map_ofNat, map_intCast] at this
      rw [this]
      push_cast
      rfl
  obtain ⟨N, hN, hNlt, hNred⟩ := key h hh
  obtain ⟨N', hN', hN'lt, hN'red⟩ := key h' hh'
  have hcast : (N : ZMod (3 ^ n)) = (N' : ZMod (3 ^ n)) := by
    change (N : ResidueGroup n) = (N' : ResidueGroup n)
    rw [hNred, hN'red, hred]
  have hNN : N = N' := by
    have := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hNlt,
      Nat.mod_eq_of_lt hN'lt] at this
  have hoff : off h = off h' := by
    have h2 : (2 : ℚ) ^ l ≠ 0 := by positivity
    apply mul_right_cancel₀ h2
    rw [hN, hN', hNN]
  exact off_injective_of_length_eq
    ((length_of_mem_mxHeadGate hh).trans (length_of_mem_mxHeadGate hh').symm) hoff

end CollatzPosDens
