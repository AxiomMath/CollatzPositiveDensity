/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrTreePolicy
public import CollatzPosDens.Transfer.EpsStar
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The white-test policy

For `ω ∈ ℕ`, integers `C`, `H'` and `m`, and reals `a ≤ b`, the *white-test policy*
`W^{ω,C,H'}_{m,a,b}` is the set of triples `(r, h, c) ∈ ℕ × ℕ × ℕ` with `2 ≤ c ≤ C` and
`h + c ≤ H'` such that `c ∉ {4, 5}`, or `h + c ≤ ω`, or
`dist(9^r (2^ω m + (a + b)/2) / 2^{h+c}, ℤ) - 9^r (b - a) / 2^{h+c+1} > ε_*`.

The third alternative is a certified white test: if the phase `α` of a black point lies in
`[a, b]`, then the point reached by the continuation `(r, h, c)` has angle at distance more
than `ε_*` from `ℤ`, so it is not black. Every white-test policy is a bounded policy.

## Main definitions

* `CollatzPosDens.trWhitePolicy ω C H' m a b`: the white-test policy `W^{ω,C,H'}_{m,a,b}`.

## Main results

* `CollatzPosDens.mem_trWhitePolicy`: the membership condition, unfolded.
* `CollatzPosDens.isBoundedPolicy_trWhitePolicy`: `W^{ω,C,H'}_{m,a,b}` is a bounded policy.
* `CollatzPosDens.trWhitePolicy_test`: a triple of the policy with `c ∈ {4, 5}` and
  `h + c > ω` passes the white test.
* `CollatzPosDens.trWhitePolicy_mono`: the policy is monotone in `C` and `H'`.

## Implementation notes

The distance `dist(y, ℤ) = min_{k ∈ ℤ} |y - k|` is written `|y - round y|`; the minimum is
attained at `round y` (`round_le`). The definition is stated for all reals `a`, `b`, with no
hypothesis `a ≤ b`.

## References

* [Mazur, *Collatz positive density*], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- The *white-test policy* `W^{ω,C,H'}_{m,a,b}`: the triples `(r, h, c)` with `2 ≤ c ≤ C`
and `h + c ≤ H'` such that `c ∉ {4, 5}`, or `h + c ≤ ω`, or
`dist(9^r (2^ω m + (a + b)/2) / 2^{h+c}, ℤ) - 9^r (b - a) / 2^{h+c+1} > ε_*`, where
`dist(y, ℤ) = |y - round y|`. -/
@[collatz_pos_dens "def_tr_white_policy"]
noncomputable def trWhitePolicy (ω : ℕ) (C H' m : ℤ) (a b : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {p | 2 ≤ p.2.2 ∧ (p.2.2 : ℤ) ≤ C ∧ ((p.2.1 + p.2.2 : ℕ) : ℤ) ≤ H' ∧
    (p.2.2 ∉ ({4, 5} : Set ℕ) ∨ p.2.1 + p.2.2 ≤ ω ∨
      (epsStar : ℝ) <
        |(9 : ℝ) ^ p.1 * (2 ^ ω * m + (a + b) / 2) / 2 ^ (p.2.1 + p.2.2) -
            round ((9 : ℝ) ^ p.1 * (2 ^ ω * m + (a + b) / 2) / 2 ^ (p.2.1 + p.2.2))| -
          (9 : ℝ) ^ p.1 * (b - a) / 2 ^ (p.2.1 + p.2.2 + 1))}

/-- Membership in the white-test policy, unfolded. -/
theorem mem_trWhitePolicy {ω : ℕ} {C H' m : ℤ} {a b : ℝ} {r h c : ℕ} :
    (r, h, c) ∈ trWhitePolicy ω C H' m a b ↔
      2 ≤ c ∧ (c : ℤ) ≤ C ∧ ((h + c : ℕ) : ℤ) ≤ H' ∧
        (c ∉ ({4, 5} : Set ℕ) ∨ h + c ≤ ω ∨
          (epsStar : ℝ) <
            |(9 : ℝ) ^ r * (2 ^ ω * m + (a + b) / 2) / 2 ^ (h + c) -
                round ((9 : ℝ) ^ r * (2 ^ ω * m + (a + b) / 2) / 2 ^ (h + c))| -
              (9 : ℝ) ^ r * (b - a) / 2 ^ (h + c + 1)) :=
  Iff.rfl

/-- Every triple `(r, h, c)` of the white-test policy has `c ≥ 2`. -/
theorem two_le_of_mem_trWhitePolicy {ω : ℕ} {C H' m : ℤ} {a b : ℝ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ trWhitePolicy ω C H' m a b) : 2 ≤ p.2.2 :=
  hp.1

/-- Every triple `(r, h, c)` of the white-test policy has `c ≤ C`. -/
theorem le_of_mem_trWhitePolicy {ω : ℕ} {C H' m : ℤ} {a b : ℝ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ trWhitePolicy ω C H' m a b) : (p.2.2 : ℤ) ≤ C :=
  hp.2.1

/-- Every triple `(r, h, c)` of the white-test policy has `h + c ≤ H'`. -/
theorem add_le_of_mem_trWhitePolicy {ω : ℕ} {C H' m : ℤ} {a b : ℝ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ trWhitePolicy ω C H' m a b) : ((p.2.1 + p.2.2 : ℕ) : ℤ) ≤ H' :=
  hp.2.2.1

/-- A triple `(r, h, c)` of the white-test policy with `c ∈ {4, 5}` and `ω < h + c` passes
the white test. -/
theorem trWhitePolicy_test {ω : ℕ} {C H' m : ℤ} {a b : ℝ} {r h c : ℕ}
    (hp : (r, h, c) ∈ trWhitePolicy ω C H' m a b) (hc : c ∈ ({4, 5} : Set ℕ))
    (hω : ω < h + c) :
    (epsStar : ℝ) <
      |(9 : ℝ) ^ r * (2 ^ ω * m + (a + b) / 2) / 2 ^ (h + c) -
          round ((9 : ℝ) ^ r * (2 ^ ω * m + (a + b) / 2) / 2 ^ (h + c))| -
        (9 : ℝ) ^ r * (b - a) / 2 ^ (h + c + 1) := by
  rcases hp.2.2.2 with h1 | h1 | h1
  · exact absurd hc h1
  · exact absurd h1 (Nat.not_le.mpr hω)
  · exact h1

/-- The white-test policy `W^{ω,C,H'}_{m,a,b}` is a bounded policy, with bound
`H'.toNat`. -/
theorem isBoundedPolicy_trWhitePolicy (ω : ℕ) (C H' m : ℤ) (a b : ℝ) :
    IsBoundedPolicy (trWhitePolicy ω C H' m a b) := by
  refine ⟨H'.toNat, fun p hp => ⟨hp.1, ?_⟩⟩
  have := hp.2.2.1
  omega

/-- The white-test policy is monotone in the bounds `C` and `H'`. -/
theorem trWhitePolicy_mono {ω : ℕ} {C₁ C₂ H₁ H₂ m : ℤ} {a b : ℝ} (hC : C₁ ≤ C₂)
    (hH : H₁ ≤ H₂) : trWhitePolicy ω C₁ H₁ m a b ⊆ trWhitePolicy ω C₂ H₂ m a b :=
  fun _ hp => ⟨hp.1, hp.2.1.trans hC, hp.2.2.1.trans hH, hp.2.2.2⟩

/-- A triple with `2 ≤ c ≤ C`, `h + c ≤ H'` and `c ∉ {4, 5}` lies in the white-test
policy. -/
theorem mem_trWhitePolicy_of_not_mem {ω : ℕ} {C H' m : ℤ} {a b : ℝ} {r h c : ℕ}
    (h2 : 2 ≤ c) (hC : (c : ℤ) ≤ C) (hH : ((h + c : ℕ) : ℤ) ≤ H')
    (hc : c ∉ ({4, 5} : Set ℕ)) : (r, h, c) ∈ trWhitePolicy ω C H' m a b :=
  ⟨h2, hC, hH, Or.inl hc⟩

/-- A triple with `2 ≤ c ≤ C`, `h + c ≤ H'` and `h + c ≤ ω` lies in the white-test policy. -/
theorem mem_trWhitePolicy_of_le {ω : ℕ} {C H' m : ℤ} {a b : ℝ} {r h c : ℕ}
    (h2 : 2 ≤ c) (hC : (c : ℤ) ≤ C) (hH : ((h + c : ℕ) : ℤ) ≤ H')
    (hω : h + c ≤ ω) : (r, h, c) ∈ trWhitePolicy ω C H' m a b :=
  ⟨h2, hC, hH, Or.inr (Or.inl hω)⟩

end CollatzPosDens
