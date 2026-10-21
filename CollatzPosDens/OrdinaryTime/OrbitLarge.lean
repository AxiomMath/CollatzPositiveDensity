/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.OrdinaryTime.S07FullWord
public import CollatzPosDens.OrdinaryTime.S07SelectedPair
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.Maps.ConcatAdmissible
public import CollatzPosDens.Maps.S01ConcatOrbit
public import CollatzPosDens.Recipe.TargetFloor

/-!
# The inverse orbit of a full word stays large

Let `t₁` be an odd integer with `t₁ ≥ targetFloor`, that is `t₁ ≥ 16^{16544}`, `n` a natural
number, `X` real, and `(h, w)` a selected pair of level `(t₁, n, X)` with full word `𝐰` of length
`d`. Then the inverse orbit `R₀ = t₁, R₁, …, R_d` of `𝐰` from `t₁` satisfies `R_i ≥ 4096` for
every `0 ≤ i ≤ d`.

The full word is the concatenation of the blocks `w_0, …, w_{n-1}, w`. The block `w_j` starts at
the generation-`j` endpoint `R_j(h) ≥ 16^{scale j}` and lies in a first-crossing family of scale
`scale j`, so has length at most `hb (scale j) = scale j + ⌊3 · scale j / 5⌋`. One inverse step
`R ↦ (2^a R - 1)/3` with `a ≥ 1` at least halves `R ≥ 2`, so along the block the orbit stays
above `16^{scale j} / 2^{hb (scale j)} ≥ 2^{12}`, using `scale j ≥ 16544`.

## Main results

* `CollatzPosDens.four_thousand_ninety_six_le_inverseOrbit_fullWord`: the orbit bound.

## Implementation notes

The orbit is bounded from below through the halving bound for the inverse step,
`(2^a R - 1)/3 ≥ R/2` for `a ≥ 1` and `R ≥ 2`, which is equivalent to the forward bound
`S(y) ≤ 2y` for the Syracuse map. The positivity of `X` is not needed, so the statement is made
for every real `X`.

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
    have ha : 1 ≤ a := v[i].pos
    have h2i : (2 : ℚ) ^ (i + 1) ≤ 2 ^ v.length := pow_le_pow_right₀ (by norm_num) hlt
    have hpos : (0 : ℚ) < 2 ^ i := by positivity
    have hx : 2 ≤ x := by
      have : (2 : ℚ) ^ i * 2 * 2 ≤ 2 ^ i * x := by
        rw [pow_succ] at h2i; linarith
      nlinarith
    have h2a : (2 : ℚ) * x ≤ 2 ^ a * x := by
      have : (2 : ℚ) ≤ 2 ^ a := by
        calc (2 : ℚ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) ha
      nlinarith
    have hstep : x / 2 ≤ (2 ^ a * x - 1) / 3 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
    calc R ≤ 2 ^ i * x := ih
      _ = 2 ^ (i + 1) * (x / 2) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (i + 1) * ((2 ^ a * x - 1) / 3) := by gcongr

/-- A block `v` with `|v| + 12 ≤ 4b`, started from `R ≥ 16^b`, keeps its inverse orbit above
`4096`. -/
private theorem orbitLarge_block {v : Word} {R : ℚ} {b : ℕ}
    (hv : v.length + 12 ≤ 4 * b) (hR : (16 : ℚ) ^ b ≤ R) {i : ℕ} (hi : i ≤ v.length) :
    4096 ≤ inverseOrbit v R i := by
  have h16 : (16 : ℚ) ^ b = 2 ^ (4 * b) := by rw [pow_mul]; norm_num
  have hbig : (2 : ℚ) ^ v.length * 4096 ≤ R := by
    calc (2 : ℚ) ^ v.length * 4096 = 2 ^ (v.length + 12) := by rw [pow_add]; norm_num
      _ ≤ 2 ^ (4 * b) := pow_le_pow_right₀ (by norm_num) hv
      _ ≤ R := h16 ▸ hR
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

/-- A block of a first-crossing family at the scale `scale j`, started from `R ≥ 16^{scale j}`,
keeps its inverse orbit above `4096`. -/
private theorem orbitLarge_firstCrossing_block {v : Word} {R : ℚ} {j : ℕ} {u : ℤ} {K : ℕ}
    (hv : v ∈ firstCrossing (scale j) u K) (hR : (16 : ℚ) ^ scale j ≤ R) :
    ∀ i ≤ v.length, 4096 ≤ inverseOrbit v R i := fun _ hi => by
  have hlen := length_le_hb_of_mem_firstCrossing hv
  have h9 := sixteen544_le_scale j
  rw [hb_eq] at hlen
  exact orbitLarge_block (by omega) hR hi

/-- **The inverse orbit of a full word stays large**. Let `t₁` be an odd integer with
`t₁ ≥ targetFloor`, `n` a natural number, `X` real, and `(h, w)` a selected pair of level
`(t₁, n, X)` with full word `𝐰` of length `d`. Then the inverse orbit `R₀ = t₁, R₁, …, R_d` of `𝐰`
from `t₁` satisfies `R_i ≥ 4096` for every `0 ≤ i ≤ d`. -/
@[collatz_pos_dens "lem_orbit_large"]
theorem four_thousand_ninety_six_le_inverseOrbit_fullWord {t₁ : ℤ} (hodd : Odd t₁)
    (ht₁ : (targetFloor : ℤ) ≤ t₁) {X : ℝ} {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X t₁ h w) {i : ℕ} (hi : i ≤ (fullWord h w).length) :
    4096 ≤ inverseOrbit (fullWord h w) t₁ i := by
  have hh := hp.mem_centralHistories
  have hend : ∀ j ≤ n, (16 : ℚ) ^ scale j ≤ historyEndpointAt t₁ h j := by
    intro j hj
    obtain ⟨m, hm, -, hmge⟩ := historyEndpointAt_large hodd ht₁ hh hj
    rw [hm]; exact_mod_cast hmge
  have ht₀ : (4096 : ℚ) ≤ t₁ := by
    have : (4096 : ℤ) ≤ t₁ :=
      calc (4096 : ℤ) = 16 ^ 3 := by norm_num
        _ ≤ 16 ^ 16544 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        _ ≤ t₁ := targetFloor_le_iff.1 ht₁
    exact_mod_cast this
  have hpre : ∀ k ≤ n, ∀ i ≤ ((List.ofFn h).take k).flatten.length,
      (4096 : ℚ) ≤ inverseOrbit ((List.ofFn h).take k).flatten t₁ i := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      simp only [List.take_zero, List.flatten_nil, List.length_nil, Nat.le_zero] at hi
      subst hi
      rw [inverseOrbit_zero]
      exact ht₀
    | succ k ih =>
      intro hk
      have hkn : k < n := hk
      rw [flatten_take_succ_ofFn h hkn]
      refine orbitLarge_append (ih hkn.le) ?_
      have hR := hend k hkn.le
      rw [historyEndpointAt] at hR
      exact orbitLarge_firstCrossing_block
        (centralFamily_subset_firstCrossing _ _
          (selectedTuples_mem_centralFamily hh.1 ⟨k, hkn⟩)) hR
  have hfull : ((List.ofFn h).take n).flatten = concatWord h := by
    rw [List.take_of_length_le List.length_ofFn.le, concatWord]
  rw [fullWord] at hi ⊢
  refine orbitLarge_append (hfull ▸ hpre n le_rfl) ?_ i hi
  have hR := hend n le_rfl
  rw [historyEndpointAt, hfull] at hR
  exact orbitLarge_firstCrossing_block hp.mem_firstCrossing hR

end CollatzPosDens
