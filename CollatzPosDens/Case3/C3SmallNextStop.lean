/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageHold
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrNextStop

/-!
# After a small gap the next stop comes quickly

Let `ι ∈ 𝔍` be a Fourier index, `J = ⌊n/2⌋`, `ξ ∈ G_n`, and let black, white and `l_*` refer to
`(n, ξ, ε_*)`. Let `e ∈ 𝒫` and `m ∈ ℕ` with `j(e) + m = J`, assume `P_*(ι) ≤ J`, and let
`a = ((r, ℓ), β) ∈ 𝒜_n` with `β` live and `a ∈ Low^e(ι) \ Bad^e_m(ι)`. Write `y_u = y^e_u(a)`,
`h = h^st_G(ι) = ⌈G/4⌉ + T_*(ι) + 1` and `h_1 = ⌈G/4⌉`. If `q + h ≤ P_*(ι) - 1` and
`gap(y_q) < G`, then some `c` with `q < c ≤ q + h` and `c < J` has `y_c` black and
`l(y_c) > l_*(y_q)`.

* *Above the top.* Along the live path the height grows by at least `4` per step up to time
  `J`, so for `u ≥ q + h_1` we get `l(y_u) - l(y_q) ≥ 4 h_1 ≥ G > gap(y_q)`, that is
  `l(y_u) > l(y_q) + gap(y_q) = l_*(y_q)`.
* *A black point in the window.* The window `{q + h_1 + 1, …, q + h_1 + T_*(ι) + 1}` has
  `T_*(ι) + 1` elements, all at most `P_*(ι) - 1`. The weighted white count `N^e_{P_*(ι)-1}(a)`
  bounds the number of white times and is at most `T_*(ι)` on `Low^e(ι)`, so some `c` in the
  window has `y_c` not white; outside `Bad^e_m(ι)` the path stays at level at most `J` up to
  time `P_*(ι)`, so `y_c` is black.

## Main results

* `CollatzPosDens.exists_bkBlack_trFreshPath_bkColTop_lt_of_trGap_lt`: after a time `q` with
  `gap(y_q) < G` the path meets a black point `y_c` with `q < c ≤ q + h^st_G(ι)`, `c < J` and
  `l(y_c) > l_*(y_q)`.

## Implementation notes

The time `c` is a natural number: it exceeds `q ≥ 0`, so this is the same as asking for an
integer. The membership `a ∈ 𝒜_n` is part of `a ∈ Low^e(ι)`, and liveness of `β` is
`TrLive a.2`. The hypotheses `n ≥ 1`, `ξ` a unit, `y_q` black and `e ∈ 𝒫` are not needed and
are omitted.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- On `Low^e(ι)` with `P_*(ι) ≤ ⌊n/2⌋`, every window `{w + 1, …, w + T_*(ι) + 1}` with
`w + T_*(ι) + 1 ≤ P_*(ι) - 1` contains a time `c` with `y^e_c(a)` not white. -/
private theorem exists_not_isBkWhite_trFreshPath_window {ι : FIndex} {n : ℕ}
    {ξ : ResidueGroup n} {e : ℤ × ℤ} (hP : pStar ι ≤ n / 2)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hlow : a ∈ trLow ι n ξ e) {w : ℕ}
    (hw : w + tStar ι + 1 ≤ pStar ι - 1) :
    ∃ c, w < c ∧ c ≤ w + tStar ι + 1 ∧
      ¬IsBkWhite n ξ (epsStar : ℝ) (trFreshPath e a c) := by
  have hlen : a.2.length = n / 2 := trAtoms_length hlow.1
  by_contra! hall
  have hsub : Finset.Icc (w + 1) (w + tStar ι + 1) ⊆
      (Finset.Icc 1 (pStar ι - 1)).filter fun i =>
        IsBkWhite n ξ (epsStar : ℝ) (trPath (bkJ e + a.1.1, bkL e + a.1.2) a.2 i) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hall i (by omega) hi.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hcnt := card_white_le_trCount (n := n) (ξ := ξ) (bkJ e + a.1.1, bkL e + a.1.2) a.2
    (fun _ hb => trAtoms_closing_mem hlow.1 hb) (t := pStar ι - 1) (by omega)
  have hlow' := trWhiteCount_le_of_mem_trLow hlow
  rw [trWhiteCount_def] at hlow'
  have : w + tStar ι + 1 + 1 - (w + 1) ≤ tStar ι := by
    exact_mod_cast (Nat.cast_le.2 hcard).trans (hcnt.trans hlow')
  omega

/-- **After a small gap the next stop comes quickly.** Let `ι ∈ 𝔍`, `J = ⌊n/2⌋`, `ξ ∈ G_n`,
`e` and `m ∈ ℕ` with `j(e) + m = J`, `P_*(ι) ≤ J`, and `a = ((r, ℓ), β)` with `β` live and
`a ∈ Low^e(ι) \ Bad^e_m(ι)`. Let `G ∈ ℕ` and `q ∈ ℕ` with `q + h^st_G(ι) ≤ P_*(ι) - 1` and
`gap(y^e_q(a)) < G`. Then some `c` with `q < c ≤ q + h^st_G(ι)` and `c < J` has `y^e_c(a)`
black and `l(y^e_c(a)) > l_*(y^e_q(a))`; black, white, `gap` and `l_*` refer to `(n, ξ, ε_*)`. -/
@[collatz_pos_dens "lem_c3_small_next_stop"]
theorem exists_bkBlack_trFreshPath_bkColTop_lt_of_trGap_lt {ι : FIndex} {n : ℕ}
    {ξ : ResidueGroup n} {e : ℤ × ℤ} {m : ℕ} (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ))
    (hP : pStar ι ≤ n / 2) {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hlive : TrLive a.2)
    (hlow : a ∈ trLow ι n ξ e) (hbad : a ∉ trBad ι n e m) {G q : ℕ}
    (hqh : q + trStageHold ι G ≤ pStar ι - 1)
    (hgap : trGap n ξ (epsStar : ℝ) (trFreshPath e a q) < G) :
    ∃ c : ℕ, q < c ∧ c ≤ q + trStageHold ι G ∧ c < n / 2 ∧
      BkBlack n ξ (epsStar : ℝ) (trFreshPath e a c) ∧
      bkColTop n ξ (epsStar : ℝ) (trFreshPath e a q) < bkL (trFreshPath e a c) := by
  have ha : a ∈ trAtoms n := hlow.1
  have hlen : a.2.length = n / 2 := trAtoms_length ha
  have hhold := add_four_mul_le_four_mul_trStageHold ι G
  have hdef := trStageHold_def ι G
  set h₁ := G ⌈/⌉ 4
  obtain ⟨c, hwc, hcw, hcwh⟩ :=
    exists_not_isBkWhite_trFreshPath_window (w := q + h₁) hP hlow (by omega)
  have hjc : bkJ (trFreshPath e a c) ≤ ((n / 2 : ℕ) : ℤ) :=
    bkJ_trFreshPath_le_of_notMem_trBad hm ha hbad (by omega)
  refine ⟨c, by omega, by omega, by omega, ⟨hjc, not_lt.1 fun hlt => hcwh ⟨hjc, hlt⟩⟩, ?_⟩
  -- the height gain from `q` to `c` is at least `4 h₁ ≥ G > gap(y_q)`
  have hgrow := trPath_bkL_sub_ge (bkJ e + a.1.1, bkL e + a.1.2) (four_le_of_mem_trAtoms ha)
    hlive (show q ≤ c by omega)
  have hminq : min q a.2.length = q := by omega
  have hminc : q + h₁ ≤ min c a.2.length := by omega
  rw [hminq] at hgrow
  have htop := bkColTop_eq_add_trGap n ξ (epsStar : ℝ) (trFreshPath e a q)
  simp only [trFreshPath] at htop hgap ⊢
  have : ((q + h₁ : ℕ) : ℤ) ≤ ((min c a.2.length : ℕ) : ℤ) := Nat.cast_le.2 hminc
  push_cast at this
  omega

end CollatzPosDens
