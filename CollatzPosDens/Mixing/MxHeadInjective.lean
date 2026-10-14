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
public import CollatzPosDens.Mixing.MxOffsetInjective

/-!
# Heads are separated modulo `3 ^ n`

Let `k, l ∈ ℕ` and `h, h' ∈ Hd(n, k, l)` with `[off(h)]_n = [off(h')]_n`. Then `h = h'`.

Since `A(h) = l`, the cleared offset `N = 2 ^ l off(h)` is a natural number, and likewise
`N' = 2 ^ l off(h')`. Reduction modulo `3 ^ n` is a ring homomorphism on `ℤ[1/2]`, so
`[N]_n = [2 ^ l]_n [off(h)]_n = [2 ^ l]_n [off(h')]_n = [N']_n`, that is `N ≡ N' (mod 3 ^ n)`.
Both are below `3 ^ n` by the product condition of the head gate, hence `N = N'` and
`off(h) = off(h')`.
As both words have length `k + 1`, injectivity of the offset on words of a fixed length gives
`h = h'`.

## Main results

* `CollatzPosDens.eq_of_dyadicRed_off_eq_of_mem_mxHeadGate`: two heads in `Hd(n, k, l)`
  with the same offset modulo `3 ^ n` are equal.

## Implementation notes

The source assumes `n ≥ 1`. The product condition `2 ^ l off(h) < 3 ^ n` is part of the
gate for every `n`, so the lemma is stated without that hypothesis.

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
  -- The cleared offset `2 ^ l off(w)` of a head is a natural number below `3 ^ n` whose
  -- reduction is `[off(w)]_n [2 ^ l]_n`.
  have key : ∀ w ∈ mxHeadGate n k l, ∃ N : ℕ, off w * 2 ^ l = N ∧ N < 3 ^ n ∧
      (N : ResidueGroup n) = dyadicRed n ⟨off w, off_mem_dyadicRationals w⟩ * 2 ^ l := by
    intro w hw
    have hlen := length_of_mem_mxHeadGate hw
    obtain ⟨N, -, hN⟩ :=
      exists_odd_off_mul_two_pow_valSum (List.ne_nil_of_length_pos (by omega) : w ≠ [])
    rw [valSum_of_mem_mxHeadGate hw] at hN
    refine ⟨N, hN, ?_, ?_⟩
    · have hb := two_pow_mul_off_lt_of_mem_mxHeadGate hw
      rw [mul_comm, hN] at hb
      exact_mod_cast hb
    · have he : (⟨off w, off_mem_dyadicRationals w⟩ : dyadicRationals) * 2 ^ l =
          ((N : ℤ) : dyadicRationals) :=
        Subtype.ext (by simpa [show ((2 : dyadicRationals) : ℚ) = 2 from rfl] using hN)
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
  exact off_injective_of_length_eq
    ((length_of_mem_mxHeadGate hh).trans (length_of_mem_mxHeadGate hh').symm)
    (mul_right_cancel₀ (by positivity : (2 : ℚ) ^ l ≠ 0) (by rw [hN, hN', hNN]))

end CollatzPosDens
