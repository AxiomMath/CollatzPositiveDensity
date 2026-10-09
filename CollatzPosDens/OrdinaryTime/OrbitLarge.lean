/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.OrdinaryTime.FullWord
public import CollatzPosDens.OrdinaryTime.SelectedPair
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.ConcatOrbit

/-!
# The inverse orbit of a full word stays large

Let `M` be a good seed, `n ∈ ℕ`, `X > 0`, and `(h, w)` a selected pair of level `(M, n, X)`
with full word `𝐰` of length `d`. Then the inverse orbit `R₀ = M, R₁, …, R_d` of `𝐰` from `M`
satisfies `R_i ≥ 4096` for every `0 ≤ i ≤ d`.

The full word is the concatenation of the blocks `w₀, …, w_{n-1}, w`. The block `w_j` starts
at the generation-`j` endpoint `R_j(h) ≥ 16^{b_j}` and lies in a first-crossing family of scale
`b_j`, so has length at most `h_{b_j} = b_j + ⌊3 b_j / 5⌋`. One inverse step
`R ↦ (2^a R - 1)/3` with `a ≥ 1` at least halves `R ≥ 2`, so along the block the orbit stays
above `16^{b_j} / 2^{h_{b_j}} ≥ 2^{12}`, using `b_j ≥ b₀ = 9`.

## Main results

* `CollatzPosDens.four_thousand_ninety_six_le_inverseOrbit_fullWord`: for a good seed `M` and a
  selected pair of level `(M, n, X)`, the inverse orbit of its full word from `M` stays `≥ 4096`.
* `CollatzPosDens.four_thousand_ninety_six_le_inverseOrbit_fullWord_of_odd`: the same bound
  for any odd integer `M ≥ 16^{b₀}` and any real `X`.

## Implementation notes

The orbit can be bounded from below by running the Syracuse map forwards, `S(y) ≤ 2y`. Here the
same halving bound is read off the inverse step directly: `(2^a R - 1)/3 ≥ R/2` for `a ≥ 1` and
`R ≥ 2`. Only the clauses `M` odd and `16^{b₀} < M` of a good seed, and no condition on `X`, are
used; the general form is stated for an odd integer `M ≥ 16^{b₀}` and an arbitrary real `X`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ}

/-- Along a word `v` started from `R ≥ 2 · 2^{|v|}`, the inverse orbit loses at most a factor
`2` per step: `R ≤ 2^i R_i` for `i ≤ |v|`. -/
private theorem orbitLarge_le_two_pow_mul_inverseOrbit {v : Word} {R : ℚ}
    (hR : 2 ^ v.length * 2 ≤ R) {i : ℕ} (hi : i ≤ v.length) :
    R ≤ 2 ^ i * inverseOrbit v R i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hlt : i < v.length := hi
    have ih := ih hlt.le
    rw [inverseOrbit_succ v R hlt, invStep]
    set x := inverseOrbit v R i
    set a : ℕ := (v[i] : ℕ)
    have h2i : (2 : ℚ) ^ (i + 1) ≤ 2 ^ v.length := pow_le_pow_right₀ (by norm_num) hlt
    have hpos : (0 : ℚ) < 2 ^ i := by positivity
    have hx : 2 ≤ x := by
      rw [pow_succ] at h2i
      nlinarith
    have h2a : (2 : ℚ) * x ≤ 2 ^ a * x := by
      have : (2 : ℚ) ≤ 2 ^ a := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) v[i].pos
      nlinarith
    have hstep : x / 2 ≤ (2 ^ a * x - 1) / 3 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      linarith
    calc R ≤ 2 ^ i * x := ih
      _ = 2 ^ (i + 1) * (x / 2) := by ring
      _ ≤ 2 ^ (i + 1) * ((2 ^ a * x - 1) / 3) := by gcongr

/-- A block `v` with `|v| + 12 ≤ 4b`, started from `R ≥ 16^b`, keeps its inverse orbit above
`4096`. -/
private theorem orbitLarge_block {v : Word} {R : ℚ} {b : ℕ}
    (hv : v.length + 12 ≤ 4 * b) (hR : (16 : ℚ) ^ b ≤ R) {i : ℕ} (hi : i ≤ v.length) :
    4096 ≤ inverseOrbit v R i := by
  have hbig : (2 : ℚ) ^ v.length * 4096 ≤ R :=
    calc (2 : ℚ) ^ v.length * 4096 = 2 ^ (v.length + 12) := by rw [pow_add]; norm_num
      _ ≤ 2 ^ (4 * b) := pow_le_pow_right₀ (by norm_num) hv
      _ = 16 ^ b := by rw [pow_mul]; norm_num
      _ ≤ R := hR
  have hpow : (0 : ℚ) < 2 ^ v.length := by positivity
  have key := orbitLarge_le_two_pow_mul_inverseOrbit (R := R) (by linarith) hi
  have hx : 0 < inverseOrbit v R i :=
    pos_of_mul_pos_right ((by linarith : 0 < R).trans_le key) (by positivity)
  exact le_of_mul_le_mul_left (hbig.trans (key.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hi) hx.le))) hpow

/-- If every term of the inverse orbit of `u` from `R`, and every term of the inverse orbit of
`v` from `src(u, R)`, is at least `c`, then so is every term of the inverse orbit of `u v`. -/
private theorem orbitLarge_append {u v : Word} {R c : ℚ}
    (hu : ∀ i ≤ u.length, c ≤ inverseOrbit u R i)
    (hv : ∀ i ≤ v.length, c ≤ inverseOrbit v (src u R) i) :
    ∀ i ≤ (u ++ v).length, c ≤ inverseOrbit (u ++ v) R i := by
  intro i hi
  rcases le_or_gt i u.length with hiu | hiu
  · rw [inverseOrbit_append_of_le_length u v R hiu]
    exact hu i hiu
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hiu
    rw [show u.length + j + 1 = u.length + (j + 1) by omega, inverseOrbit_append_length_add]
    exact hv _ (by simp at hi; omega)

/-- A block of a first-crossing family at a scale `b_j`, started from `R ≥ 16^{b_j}`, keeps its
inverse orbit above `4096`. -/
private theorem orbitLarge_firstCrossing_block {v : Word} {R : ℚ} {j : ℕ} {u : ℤ} {K : ℕ}
    (hv : v ∈ firstCrossing (scale j) u K) (hR : (16 : ℚ) ^ scale j ≤ R) :
    ∀ i ≤ v.length, 4096 ≤ inverseOrbit v R i := fun _ hi => by
  have hlen := length_le_hb_of_mem_firstCrossing hv
  have h9 := nine_le_scale j
  rw [hb_eq] at hlen
  exact orbitLarge_block (by omega) hR hi

/-- **The inverse orbit of a full word stays large**, for any odd integer `M ≥ 16^{b₀}`: if
`(h, w)` is a selected pair of level `(M, n, X)`, then every term `R_i`, `0 ≤ i ≤ |𝐰(h, w)|`, of
the inverse orbit of the full word `𝐰(h, w)` from `M` satisfies `R_i ≥ 4096`. -/
theorem four_thousand_ninety_six_le_inverseOrbit_fullWord_of_odd {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) {X : ℝ} {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X M h w) {i : ℕ} (hi : i ≤ (fullWord h w).length) :
    4096 ≤ inverseOrbit (fullWord h w) M i := by
  have hh := hp.mem_centralHistories
  have hend : ∀ j ≤ n, (16 : ℚ) ^ scale j ≤ historyEndpointAt M h j := by
    intro j hj
    obtain ⟨m, hm, -, hmge⟩ := historyEndpointAt_large hodd hM hh hj
    rw [hm]
    exact_mod_cast hmge
  have hpre : ∀ j ≤ n, ∀ i ≤ ((List.ofFn h).take j).flatten.length,
      (4096 : ℚ) ≤ inverseOrbit ((List.ofFn h).take j).flatten M i := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      simp only [List.take_zero, List.flatten_nil, List.length_nil, Nat.le_zero] at hi
      subst hi
      rw [inverseOrbit_zero]
      have h0 := hend 0 (Nat.zero_le _)
      rw [historyEndpointAt_zero, scale_zero] at h0
      exact le_trans (by norm_num) h0
    | succ j ih =>
      intro hj
      have hjn : j < n := hj
      rw [flatten_take_succ_ofFn h hjn]
      refine orbitLarge_append (ih hjn.le) ?_
      have hR := hend j hjn.le
      rw [historyEndpointAt] at hR
      exact orbitLarge_firstCrossing_block
        (centralFamily_subset_firstCrossing _ _
          (selectedTuples_mem_centralFamily hh.1 ⟨j, hjn⟩)) hR
  have hfull : ((List.ofFn h).take n).flatten = concatWord h := by
    rw [List.take_of_length_le (by simp), concatWord]
  rw [fullWord] at hi ⊢
  refine orbitLarge_append (hfull ▸ hpre n le_rfl) ?_ i hi
  have hR := hend n le_rfl
  rw [historyEndpointAt, hfull] at hR
  exact orbitLarge_firstCrossing_block hp.mem_firstCrossing hR

/-- **The inverse orbit of a full word stays large.** Let `M` be a good seed, `n ∈ ℕ`, `X > 0`,
and `(h, w)` a selected pair of level `(M, n, X)` with full word `𝐰` of length `d`. Then the
inverse orbit `R₀ = M, R₁, …, R_d` of `𝐰` from `M` satisfies `R_i ≥ 4096` for every `0 ≤ i ≤ d`.
-/
@[collatz_pos_dens "lem_orbit_large"]
theorem four_thousand_ninety_six_le_inverseOrbit_fullWord {M : ℕ} (hM : GoodSeed M) {X : ℝ}
    (_hX : 0 < X) {h : Fin n → Word} {w : Word} (hp : IsSelectedPair n X M h w) {i : ℕ}
    (hi : i ≤ (fullWord h w).length) :
    4096 ≤ inverseOrbit (fullWord h w) M i := by
  have hodd : Odd (M : ℤ) := by exact_mod_cast hM.odd
  have hge : (16 : ℤ) ^ scale 0 ≤ M := by exact_mod_cast hM.lower.le
  have hp' : IsSelectedPair n X ((M : ℤ) : ℚ) h w := by rwa [Int.cast_natCast]
  simpa using four_thousand_ninety_six_le_inverseOrbit_fullWord_of_odd hodd hge hp' hi

end CollatzPosDens
