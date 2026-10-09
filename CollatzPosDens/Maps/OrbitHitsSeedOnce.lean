/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.SyracuseOfInverse

/-!
# An orbit hits a seed at most once

Let `M > 1` be an odd integer with `3M + 1` a power of `2`. Then `S(M) = 1` and `S(1) = 1`, so
the Syracuse orbit of `M` never returns to `M`. Consequently, if two words `u, u'` admissible
from `M` have the same source `x`, then `S^{|u|}(x) = M = S^{|u'|}(x)` forces `|u| = |u'|`.

## Main results

* `CollatzPosDens.Admissible.exists_collatzAccel_iterate_inverseOrbit`: along a word admissible
  from a positive odd integer `R`, the term `R_i` is a natural number `m` with `S^i(m) = R`.
* `CollatzPosDens.collatzAccel_iterate_eq_one`: if `3M + 1` is a power of two, `S^j(M) = 1` for
  every `j ≥ 1`.
* `CollatzPosDens.Admissible.length_eq_of_src_eq`: two words admissible from `M` with the same
  source have the same length.

## Implementation notes

The seed `M` is an integer `M : ℤ`, cast to `ℚ` in `CollatzPosDens.Admissible`; the Syracuse map
acts on `ℕ`, and the iterates are compared after casting to `ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Along a word admissible from a positive odd integer `R`, the `i`-th term of the inverse orbit,
`i ≤ |w|`, is a natural number `m` whose `i`-th Syracuse iterate is `R`. -/
theorem Admissible.exists_collatzAccel_iterate_inverseOrbit {R : ℤ} {w : Word}
    (hw : Admissible R w) (hpos : 0 < R) (hodd : Odd R) {i : ℕ} (hi : i ≤ w.length) :
    ∃ m : ℕ, inverseOrbit w R i = m ∧ ((collatzAccel^[i] m : ℕ) : ℤ) = R := by
  induction i with
  | zero =>
    lift R to ℕ using hpos.le
    exact ⟨R, by simp, by simp⟩
  | succ i ih =>
    obtain ⟨k, hk, hkR⟩ := ih (by omega)
    obtain ⟨m, hm, hsm⟩ := hw.collatzAccel_inverseOrbit_succ hpos hodd (i := i) (by omega)
    refine ⟨m, hm, ?_⟩
    rw [hk] at hsm
    have hsm' : collatzAccel m = k := by exact_mod_cast hsm
    rw [Function.iterate_succ_apply, hsm', hkR]

/-- The source of a word admissible from a positive odd integer `R` is a natural number whose
`|w|`-th Syracuse iterate is `R`. -/
theorem Admissible.exists_collatzAccel_iterate_src {R : ℤ} {w : Word}
    (hw : Admissible R w) (hpos : 0 < R) (hodd : Odd R) :
    ∃ m : ℕ, src w R = m ∧ ((collatzAccel^[w.length] m : ℕ) : ℤ) = R := by
  simpa using hw.exists_collatzAccel_iterate_inverseOrbit hpos hodd le_rfl

/-- The Syracuse map fixes `1`. -/
theorem collatzAccel_one : collatzAccel 1 = 1 :=
  collatzAccel_eq_of_three_mul_add_one_eq (a := 2) (by norm_num) odd_one

/-- If `3M + 1` is a power of two, then every iterate `S^j(M)` with `j ≥ 1` equals `1`. -/
theorem collatzAccel_iterate_eq_one {M k j : ℕ} (hM : 3 * M + 1 = 2 ^ k) (hj : 1 ≤ j) :
    collatzAccel^[j] M = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [Function.iterate_succ_apply,
    collatzAccel_eq_of_three_mul_add_one_eq (y := 1) (by rw [hM, mul_one]) odd_one,
    Function.iterate_fixed collatzAccel_one]

/-- **The orbit hits the seed once.** Let `M > 1` be an odd integer with `3M + 1` a power of `2`.
If the words `u, u'` are both admissible from `M` and `src(u, M) = src(u', M)`, then
`|u| = |u'|`. -/
@[collatz_pos_dens "lem_orbit_hits_seed_once"]
theorem Admissible.length_eq_of_src_eq {M : ℤ} (hM : 1 < M) (hodd : Odd M)
    (hpow : ∃ k : ℕ, 3 * M + 1 = 2 ^ k) {u u' : Word} (hu : Admissible M u)
    (hu' : Admissible M u') (hsrc : src u M = src u' M) : u.length = u'.length := by
  have hpos : 0 < M := by omega
  obtain ⟨k, hk⟩ := hpow
  lift M to ℕ using hpos.le
  have hk' : 3 * M + 1 = 2 ^ k := by exact_mod_cast hk
  have hM' : 1 < M := by exact_mod_cast hM
  obtain ⟨x, hx, hxM⟩ := hu.exists_collatzAccel_iterate_src hpos hodd
  obtain ⟨x', hx', hxM'⟩ := hu'.exists_collatzAccel_iterate_src hpos hodd
  have hxx : x = x' := by exact_mod_cast hx.symm.trans (hsrc.trans hx')
  subst hxx
  have h1 : collatzAccel^[u.length] x = M := by exact_mod_cast hxM
  have h2 : collatzAccel^[u'.length] x = M := by exact_mod_cast hxM'
  have key : ∀ d d' : ℕ, collatzAccel^[d] x = M → collatzAccel^[d'] x = M → ¬ d < d' := by
    intro d d' hd hd' hlt
    have : collatzAccel^[d' - d] M = M :=
      calc collatzAccel^[d' - d] M = collatzAccel^[d' - d] (collatzAccel^[d] x) := by rw [hd]
        _ = collatzAccel^[d'] x := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
        _ = M := hd'
    rw [collatzAccel_iterate_eq_one hk' (by omega)] at this
    omega
  have := key _ _ h1 h2
  have := key _ _ h2 h1
  omega

end CollatzPosDens
