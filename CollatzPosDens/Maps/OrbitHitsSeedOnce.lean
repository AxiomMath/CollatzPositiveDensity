/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.SyracuseOfInverse
public import CollatzPosDens.Maps.SyrPeriodic

/-!
# An orbit hits a seed at most once

Let `y` be a positive odd integer that is not Syracuse-periodic. If `S^r(n) = y = S^{r'}(n)` for
some `n`, then `r = r'`: were `r < r'`, this would give `S^{r' - r}(y) = y`, so `y` would be
Syracuse-periodic. Applied to the source of words admissible from a seed `M`, two such words with
the same source have the same length.

## Main results

* `CollatzPosDens.Admissible.exists_collatzAccel_iterate_inverseOrbit`: along a word admissible
  from a positive odd integer `R`, the term `R_i` is a natural number `m` with `S^i(m) = R`.
* `CollatzPosDens.collatzAccel_one`: the Syracuse map fixes `1`.
* `CollatzPosDens.eq_of_collatzAccel_iterate_eq_of_not_syrPeriodic`: an orbit hits a
  non-periodic point at most once.
* `CollatzPosDens.Admissible.length_eq_of_src_eq`: two words admissible from `M` with the same
  source have the same length.

## Implementation notes

The main statement holds for all natural numbers `y, n`: positivity and oddness are not needed,
since `collatzAccel` is a total map on `ℕ`.

The seed is a natural number `M : ℕ`, as `SyrPeriodic` is a predicate on `ℕ`; the words are
admissible from its cast `(M : ℤ)`, matching the other statements about admissible words, and the
Syracuse iterates are compared after casting to `ℤ`.

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

/-- **The orbit hits the seed once.** If `y` is not Syracuse-periodic and `S^r(n) = y = S^{r'}(n)`,
then `r = r'`: were `r < r'`, then `S^{r' - r}(y) = S^{r'}(n) = y` would make `y` periodic. -/
@[collatz_pos_dens "lem_orbit_hits_seed_once"]
theorem eq_of_collatzAccel_iterate_eq_of_not_syrPeriodic {y n : ℕ} (hper : ¬ SyrPeriodic y)
    {r r' : ℕ} (hr : collatzAccel^[r] n = y) (hr' : collatzAccel^[r'] n = y) : r = r' := by
  -- If `d < d'`, then `S^{d' - d}(y) = y` with `d' - d ≥ 1`, so `y` is Syracuse-periodic.
  have key : ∀ d d' : ℕ, collatzAccel^[d] n = y → collatzAccel^[d'] n = y → ¬ d < d' := by
    intro d d' hd hd' hlt
    refine hper ⟨d' - d, by omega, ?_⟩
    calc collatzAccel^[d' - d] y = collatzAccel^[d' - d] (collatzAccel^[d] n) := by rw [hd]
      _ = collatzAccel^[d'] n := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
      _ = y := hd'
  have := key _ _ hr hr'
  have := key _ _ hr' hr
  omega

/-- Let `M` be a positive odd integer that is not Syracuse-periodic. If the words `u, u'` are both
admissible from `M` and `src(u, M) = src(u', M)`, then `|u| = |u'|`. -/
theorem Admissible.length_eq_of_src_eq {M : ℕ} (hpos : 0 < M) (hodd : Odd M)
    (hper : ¬ SyrPeriodic M) {u u' : Word} (hu : Admissible (M : ℤ) u)
    (hu' : Admissible (M : ℤ) u') (hsrc : src u (M : ℤ) = src u' (M : ℤ)) :
    u.length = u'.length := by
  have hpos' : (0 : ℤ) < M := by exact_mod_cast hpos
  have hodd' : Odd (M : ℤ) := by exact_mod_cast hodd
  obtain ⟨x, hx, hxM⟩ := hu.exists_collatzAccel_iterate_src hpos' hodd'
  obtain ⟨x', hx', hxM'⟩ := hu'.exists_collatzAccel_iterate_src hpos' hodd'
  have hxx : x = x' := by exact_mod_cast hx.symm.trans (hsrc.trans hx')
  subst hxx
  exact eq_of_collatzAccel_iterate_eq_of_not_syrPeriodic hper (by exact_mod_cast hxM)
    (by exact_mod_cast hxM')

end CollatzPosDens
