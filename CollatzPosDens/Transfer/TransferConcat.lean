/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Transfer.Transfer

/-!
# Transfers of a concatenation

Let `u`, `v` be words of lengths `d`, `e`, let `t ∈ ℕ`, and let `g : G_t → ℝ`. The transfer
of the concatenation `uv` is the composite of the transfers: `𝒯_{uv} g = 𝒯_u (𝒯_v g)` as
functions on `G_{t+e+d}`. This rests on the composition law `φ_u ∘ φ_v = φ_{uv}` of residue
maps `G_t → G_{t+e} → G_{t+e+d}`: the representative of `φ_v(z)` is only known modulo
`3^{t+e}`, but multiplication by `[ω(u)]_{t+e+d}`, which is `3^d` times a unit, upgrades a
congruence modulo `3^{t+e}` to one modulo `3^{t+e+d}`. Together with `ω(uv) = ω(u) ω(v)` and
`off(uv) = off(u) + ω(u) off(v)` this gives `𝒯_{uv} g = 𝒯_u (𝒯_v g)`.

## Main results

* `CollatzPosDens.residueMap_residueMap`: `φ_u (φ_v z) = φ_{uv}(z)`.
* `CollatzPosDens.transfer_append`: `𝒯_{uv} g = 𝒯_u (𝒯_v g)`.

## Implementation notes

The transfer `𝒯_{uv} g` is a function on `G_{t+|uv|}` while `𝒯_u (𝒯_v g)` is a function on
`G_{(t+|v|)+|u|}`; the two indices are equal but not definitionally so. The statements
therefore transport points of `G_{t+e+d}` along the equality of types
`G_{t+e+d} = G_{t+|uv|}` with `cast`, which on `ZMod (3 ^ k)` does not change the residue.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The affine expression `[ω(w)]_k · z̃ + [off(w)]_k` defining `φ_w`, at an arbitrary
level `k`. -/
private noncomputable def transferConcatAff (k : ℕ) (w : Word) {t : ℕ} (z : ResidueGroup t) :
    ResidueGroup k :=
  dyadicRed k ⟨w.weight, w.weight_mem_dyadicRationals⟩ * (z.val : ResidueGroup k) +
    dyadicRed k ⟨off w, off_mem_dyadicRationals w⟩

/-- Transporting along an equality of levels does not change the affine expression. -/
private theorem cast_transferConcatAff {k k' : ℕ} (hk : k = k') (w : Word) {t : ℕ}
    (z : ResidueGroup t) :
    cast (congrArg ResidueGroup hk) (transferConcatAff k w z) = transferConcatAff k' w z := by
  subst hk
  rfl

/-- Multiplying by `3^d` in `G_{M+d}`, a residue lifted from `G_M` behaves like any lift. -/
private theorem three_pow_mul_val_natCast (M d a : ℕ) :
    (3 : ResidueGroup (M + d)) ^ d * (((a : ResidueGroup M).val : ℕ) : ResidueGroup (M + d)) =
      3 ^ d * (a : ResidueGroup (M + d)) := by
  have h0 : (3 : ResidueGroup (M + d)) ^ d * 3 ^ M = 0 := by
    rw [← pow_add, Nat.add_comm d M]
    exact three_pow_self_residueGroup (M + d)
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div a (3 ^ M)]
  push_cast
  rw [mul_add, ← mul_assoc, h0, zero_mul, add_zero]

/-- The reduction of a residue of `G_{M+d}` to `G_M`, lifted back and multiplied by `3^d`,
is `3^d` times the original residue. -/
private theorem three_pow_mul_val_cast (M d : ℕ) (x : ResidueGroup (M + d)) :
    (3 : ResidueGroup (M + d)) ^ d * (((x.cast : ResidueGroup M).val : ℕ) : ResidueGroup _) =
      3 ^ d * x := by
  rw [ZMod.cast_eq_val, three_pow_mul_val_natCast, ZMod.natCast_zmod_val]

/-- The composition law of residue maps: `φ_u (φ_v z) = φ_{uv}(z)` for `z ∈ G_t`, with both
sides read in `G_{t+|v|+|u|}`. -/
theorem residueMap_residueMap (u v : Word) {t : ℕ} (z : ResidueGroup t) :
    residueMap u (t + v.length) (residueMap v t z) =
      cast (congrArg ResidueGroup (by rw [List.length_append]; ring))
        (residueMap (u ++ v) t z) := by
  have hdvd : 3 ^ (t + v.length) ∣ 3 ^ (t + v.length + u.length) :=
    pow_dvd_pow 3 (Nat.le_add_right _ _)
  have hred : (ZMod.castHom hdvd (ResidueGroup (t + v.length))).comp
      (dyadicRed (t + v.length + u.length)) = dyadicRed (t + v.length) :=
    eq_dyadicRed _
  have hv : residueMap v t z =
      ((transferConcatAff (t + v.length + u.length) v z).cast : ResidueGroup (t + v.length)) := by
    rw [← ZMod.castHom_apply (h := hdvd), transferConcatAff, map_add, map_mul, map_natCast,
      ← RingHom.comp_apply, ← RingHom.comp_apply, hred]
    rfl
  change _ = cast _ (transferConcatAff _ (u ++ v) z)
  rw [cast_transferConcatAff (by rw [List.length_append]; ring), residueMap_apply, hv,
    dyadicRed_weight, mul_comm ((3 : ResidueGroup _) ^ _), mul_assoc,
    three_pow_mul_val_cast, ← mul_assoc, mul_comm _ ((3 : ResidueGroup _) ^ _),
    ← dyadicRed_weight, transferConcatAff, transferConcatAff]
  have e1 : (⟨(u ++ v).weight, Word.weight_mem_dyadicRationals _⟩ : dyadicRationals) =
      ⟨u.weight, Word.weight_mem_dyadicRationals _⟩ *
        ⟨v.weight, Word.weight_mem_dyadicRationals _⟩ :=
    Subtype.ext (by simp)
  rw [e1, map_mul, dyadicRed_off_append]
  ring

/-- The transfer of a concatenation is the composite of the transfers:
`𝒯_{uv} g = 𝒯_u (𝒯_v g)` as functions on `G_{t+|v|+|u|}`. -/
@[collatz_pos_dens "lem_transfer_concat"]
theorem transfer_append (u v : Word) {t : ℕ} (g : ResidueGroup t → ℝ)
    (y : ResidueGroup (t + v.length + u.length)) :
    transfer (u ++ v) g (cast (congrArg ResidueGroup (by rw [List.length_append]; ring)) y) =
      transfer u (transfer v g) y := by
  simp only [transfer_apply, ← mul_sum]
  rw [← mul_assoc, ← Rat.cast_mul, ← Word.weight_append]
  congr 1
  rw [sum_fiberwise_eq_sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext z
  simp only [mem_filter, mem_univ, true_and, residueMap_residueMap]
  constructor
  · intro h
    rw [h, cast_cast, cast_eq]
  · rintro rfl
    rw [cast_cast, cast_eq]

end CollatzPosDens
