/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrTreeValid
public import CollatzPosDens.StoppingTrace.TrWhitePolicy

/-!
# White-test policies are valid

Let `v` be a black point with gap `ω = gap(v)`, and suppose the angles above and to the right
of `v` are affine in a phase `α`: for an integer `m`, a height `H ∈ ℕ` and all `r ≥ 1`,
`0 ≤ L ≤ H`,
`ϑ(v + (r, L)) - 9^{r-1} (2^ω m + α) / 2^L ∈ ℤ`.
If `a ≤ α ≤ b` and `H' ≤ H`, then the white-test policy `W^{ω,C,H'}_{m,a,b}` is valid at `v`:
for each `(r, h, c)` in it with `c ∈ {4, 5}`, the point `y = v + (r + 1, h + c)` either lies
at height at most `l_*(v) = l(v) + ω`, or its angle satisfies
`|ϑ(y)| ≥ dist(ϑ(y), ℤ) > ε_*`, so that `y` is not black.

The second alternative is the estimate
`dist(ϑ(y), ℤ) ≥ dist(9^r (2^ω m + u) / 2^{h+c}, ℤ) - 9^r δ / 2^{h+c}`, with `u = (a + b)/2`
and `δ = (b - a)/2`, which holds because `dist(·, ℤ)` is `1`-Lipschitz and `1`-periodic.

## Main results

* `CollatzPosDens.abs_sub_round_sub_le`: the Lipschitz–periodicity estimate for
  `dist(·, ℤ) = |· - round ·|`.
* `CollatzPosDens.trTreeValid_trWhitePolicy`: the white-test policy is valid at `v`.

## Implementation notes

Neither blackness of `v` nor the equality `ω = gap(v)` is used: the proof only needs
`l(v) + ω ≤ l_*(v)`, so the hypothesis is `ω ≤ gap(v)`, with `ω ∈ ℕ` as in
`CollatzPosDens.trWhitePolicy`. Validity is proved for every colour scale `ε ≤ ε_*`, not only
for `ε_*` itself. Membership in `ℤ` is written as the existence of an integer
equal to the real number.

## References

* [Mazur, *Collatz positive density*], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- The distance to `ℤ`, written `|x - round x|`, is `1`-Lipschitz and `1`-periodic: if
`x - k = θ` for an integer `k` and `|θ - θ₀| ≤ d`, then
`|θ₀ - round θ₀| - d ≤ |x - round x|`. -/
theorem abs_sub_round_sub_le {x θ θ₀ d : ℝ} {k : ℤ} (hk : x - θ = k) (hd : |θ - θ₀| ≤ d) :
    |θ₀ - round θ₀| - d ≤ |x - round x| := by
  have h1 : |θ₀ - round θ₀| ≤ |θ₀ - ((round x - k : ℤ) : ℝ)| := round_le θ₀ _
  have h2 : θ₀ - ((round x - k : ℤ) : ℝ) = (θ₀ - θ) + (x - round x) := by
    push_cast; linarith
  rw [h2] at h1
  have h3 := abs_add_le (θ₀ - θ) (x - round x)
  rw [abs_sub_comm] at hd
  linarith

/-- **White-test policies are valid.** Let `ω ≤ gap(v)`, `H ∈ ℕ`, `m ∈ ℤ` and `α ∈ ℝ` be such
that `ϑ(v + (r, L)) - 9^{r-1} (2^ω m + α) / 2^L ∈ ℤ` for all `r ≥ 1` and `0 ≤ L ≤ H`. Then for
all integers `C` and `H' ≤ H`, and reals `a ≤ α ≤ b`, the white-test policy
`W^{ω,C,H'}_{m,a,b}` is valid at `v`, for every colour scale `ε ≤ ε_*`. -/
@[collatz_pos_dens "lem_tr_white_policy_valid"]
theorem trTreeValid_trWhitePolicy {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {v : ℤ × ℤ} {ω H : ℕ}
    {m C H' : ℤ} {α a b : ℝ} (hε : ε ≤ (epsStar : ℝ)) (hω : (ω : ℤ) ≤ trGap n ξ ε v)
    (hθ : ∀ r : ℕ, 1 ≤ r → ∀ L : ℕ, L ≤ H → ∃ k : ℤ,
      bkTheta n ξ (v + ((r : ℤ), (L : ℤ))) - (9 : ℝ) ^ (r - 1) * (2 ^ ω * m + α) / 2 ^ L = k)
    (hH' : H' ≤ H) (ha : a ≤ α) (hb : α ≤ b) :
    TrTreeValid n ξ ε v (trWhitePolicy ω C H' m a b) := by
  intro r h c hm hc
  by_cases hle : h + c ≤ ω
  · right
    rw [bkL_add_natCast_pair, bkColTop_eq_add_trGap]
    have : ((h + c : ℕ) : ℤ) ≤ ω := by exact_mod_cast hle
    linarith
  · left
    have hc' : c ∈ ({4, 5} : Set ℕ) := by rcases hc with rfl | rfl <;> simp
    have htest := trWhitePolicy_test hm hc' (Nat.lt_of_not_le hle)
    have hL : h + c ≤ H := by
      have := add_le_of_mem_trWhitePolicy hm
      simp only at this
      omega
    obtain ⟨k, hk⟩ := hθ (r + 1) (Nat.le_add_left 1 r) (h + c) hL
    rw [Nat.add_sub_cancel] at hk
    apply not_bkBlack_of_lt
    set y := v + (((r + 1 : ℕ) : ℤ), ((h + c : ℕ) : ℤ))
    set θ₀ := (9 : ℝ) ^ r * (2 ^ ω * m + (a + b) / 2) / 2 ^ (h + c)
    have hpos : (0 : ℝ) < (9 : ℝ) ^ r / 2 ^ (h + c) := by positivity
    have hd : |(9 : ℝ) ^ r * (2 ^ ω * m + α) / 2 ^ (h + c) - θ₀| ≤
        (9 : ℝ) ^ r * (b - a) / 2 ^ (h + c + 1) := by
      have e1 : (9 : ℝ) ^ r * (2 ^ ω * m + α) / 2 ^ (h + c) - θ₀ =
          (9 : ℝ) ^ r / 2 ^ (h + c) * (α - (a + b) / 2) := by
        simp only [θ₀]; ring
      have e2 : (9 : ℝ) ^ r * (b - a) / 2 ^ (h + c + 1) =
          (9 : ℝ) ^ r / 2 ^ (h + c) * ((b - a) / 2) := by
        rw [pow_succ]; ring
      rw [e1, e2, abs_mul, abs_of_pos hpos]
      refine mul_le_mul_of_nonneg_left ?_ hpos.le
      rw [abs_le]
      constructor <;> linarith
    have key := abs_sub_round_sub_le hk hd
    have h0 : |bkTheta n ξ y - round (bkTheta n ξ y)| ≤ |bkTheta n ξ y| := by
      simpa using round_le (bkTheta n ξ y) 0
    linarith

end CollatzPosDens
