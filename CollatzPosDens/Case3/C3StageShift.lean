/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageEnd

/-!
# Stage end indices after a restart

Fix a level `n`, a residue `ξ ∈ G_n` and a colour scale `ε`. Let `x = (x_u)_{u ∈ ℕ}` and
`x' = (x'_u)_{u ∈ ℕ}` be sequences of points and `q, c ∈ ℕ` such that `x_{q+u} = x'_u` for every
`u ∈ ℕ`, `ν(x) = c + ν(x')` and `τ_{c+i}(x) = q + τ_i(x')` for every `1 ≤ i ≤ ν(x')`: the
stopping sequence of `x`, from its `(c+1)`-st term on, is that of `x'` shifted by `q`. Then for
all `G`, `d`, `k`, `t` and `i ≥ 1`,
```
se^{G,d}_{k,t}(x; c + i) = c + se^{G,d}_{k,t}(x'; i),
```
where `c + ∞ = ∞`. The proof is by induction on `(k, t)` in the lexicographic order, for all
`i ≥ 1` at once: for `k ≥ 1`, either `ν(x') < i` and both sides are `∞`, or the two stops
`τ_{c+i}(x) = q + τ_i(x')` see the same point `x_{q+τ_i(x')} = x'_{τ_i(x')}`, hence the same
gap and the same next state.

## Main results

* `CollatzPosDens.trStageEnd_add_of_shift`: the identity above.

## Implementation notes

The relation `τ_{c+i}(x) = q + τ_i(x')` between partially defined stopping times is stated as an
equality of `Option ℕ`, `τ_{c+i}(x) = (τ_i(x')).map (q + ·)`, for `1 ≤ i ≤ ν(x')`; there both
sides are defined. The addition `c + ∞ = ∞` is that of `ℕ∞`. The identity holds without the
hypotheses `G ≥ 0`, `d ≥ 1` and `1 ≤ t ≤ d`, which are therefore not assumed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {G : ℤ} {d : ℕ}

/-- **Stage end indices after a restart.** If `x_{q+u} = x'_u` for every `u`,
`ν(x) = c + ν(x')` and `τ_{c+i}(x) = q + τ_i(x')` for `1 ≤ i ≤ ν(x')`, then
`se^{G,d}_{k,t}(x; c + i) = c + se^{G,d}_{k,t}(x'; i)` for all `k`, `t` and `i ≥ 1`. -/
@[collatz_pos_dens "lem_c3_stage_shift"]
theorem trStageEnd_add_of_shift {x x' : ℕ → ℤ × ℤ} {q c : ℕ} (hx : ∀ u, x (q + u) = x' u)
    (hν : trNu n ξ ε x = c + trNu n ξ ε x')
    (hτ : ∀ i, 1 ≤ i → i ≤ trNu n ξ ε x' →
      trStopTime n ξ ε x (c + i) = (trStopTime n ξ ε x' i).map (q + ·)) :
    ∀ k t i : ℕ, 1 ≤ i →
      trStageEnd n ξ ε G d x k t (c + i) = c + trStageEnd n ξ ε G d x' k t i
  | 0, t, i, _ => by simp
  | k + 1, t, i, hi => by
    by_cases hlt : trNu n ξ ε x' < i
    · rw [trStageEnd_of_trNu_lt (Nat.le_add_left 1 k) t hlt,
        trStageEnd_of_trNu_lt (Nat.le_add_left 1 k) t (by omega), add_top]
    · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
        (isSome_trStopTime_iff (n := n) (ξ := ξ) (ε := ε) (x := x') (i := i) |>.2
          ⟨hi, not_lt.1 hlt⟩)
      have hs' : trStopTime n ξ ε x (c + i) = some (q + s) := by
        rw [hτ i hi (not_lt.1 hlt), hs, Option.map_some]
      rw [trStageEnd_of_trStopTime_eq_some (Nat.le_add_left 1 k) t hs',
        trStageEnd_of_trStopTime_eq_some (Nat.le_add_left 1 k) t hs, hx s, add_assoc]
      exact trStageEnd_add_of_shift hx hν hτ _ _ (i + 1) (Nat.le_add_left 1 i)
termination_by k t _ _ => (k, t)
decreasing_by exact trStageNext_lt (Nat.le_add_left 1 k)

end CollatzPosDens
