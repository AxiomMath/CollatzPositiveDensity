/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CycInterval
public import CollatzPosDens.Renewal.RnBinomRow
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.Renewal.RnRawOddSum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Packing a periodic weight against a renewal row

Let `g : ℕ → ℝ` be nonnegative and `L`-periodic, with mean `μ` over a period and with `D` the
range (maximum minus minimum over `0 ≤ k ≤ L`) of its centred partial sums. Let `Z ⊆ ℤ` be a set
whose distinct points are at distance at least `d₀ ≥ N`, and `V` the union of the blocks
`{z, …, z + N - 1}`, `z ∈ Z`. Then for `l ≥ 2` the row `r ↦ 𝖱(r - 1, l)` of raw-prefix masses
satisfies
$$\sum_{r \in V,\ r \ge 1} 𝖱(r - 1, l)\, g(r + a) \le (\mu N + D)
  \Bigl(\Bigl(1 + \frac{N - 2}{d_0}\Bigr)\frac{1}{\sqrt{2(3l - 1)}} + \frac{1}{4 d_0}\Bigr).$$

The proof is a layer-cake decomposition of the row. The row `b(r) = 𝖱(r - 1, l)` vanishes at
`r ≤ 1`, equals `binom(l - 1, 2r - 3) 2^{-l}` for `r ≥ 2`, sums to `1/4`, and has maximum at most
`(2(3l - 1))^{-1/2}`; unimodality of the binomial coefficients makes `b` quasi-concave, i.e. its
superlevel sets are intervals. An interval `I` of `t` consecutive integers meets at most
`1 + (t + N - 2) / d₀` blocks, since the starts of those blocks lie in an interval of length
`t + N - 2`; each block contributes at most `μ N + D` to the sum of `g(· + a)` over `I ∩ V`.

## Main results

* `CollatzPosDens.min_choose_le_choose`: the binomial coefficients of a row are quasi-concave.
* `CollatzPosDens.sum_Ico_mul_le_of_quasiConcave`: if every interval sum of `w` is at most
  `A + B t`, then `∑ b w ≤ A max b + B ∑ b` for a nonnegative quasi-concave `b`.
* `CollatzPosDens.card_sub_one_mul_le_of_separated`: a `d`-separated finite set of integers in
  `[x, y]` has at most `1 + (y - x) / d` points.
* `CollatzPosDens.sum_Ico_ite_mem_blocks_le`: the interval-sum bound for `g` restricted to a union
  of separated blocks, `(1 + (t + N - 2) / d₀) (μ N + D)` over `t` consecutive integers.
* `CollatzPosDens.sum_rawMass_mul_periodic_le`: the packing bound, for every finite part of `V`.
* `CollatzPosDens.tsum_rawMass_mul_periodic_le`: the packing bound for the sum over all of `V`,
  together with its summability.

## Implementation notes

The weight `g` is only assumed nonnegative, rather than `[0, 1]`-valued. The sum over `V` has
finitely many nonzero terms, since the row vanishes for `r ≥ l + 2`, but `Z` may be infinite. The
bound is stated both for every finite subset of `V` (`sum_rawMass_mul_periodic_le`) and as a
summable unconditional sum over `V ∩ [1, ∞)` (`tsum_rawMass_mul_periodic_le`). The layer-cake
decomposition is carried out as an induction on the length of the support: subtracting the
smaller endpoint value removes one endpoint and keeps quasi-concavity.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The binomial coefficients `n.choose a` increase in `a` up to `n / 2`. -/
theorem choose_le_choose_of_le_half {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- The binomial coefficients of a row are quasi-concave: for `x ≤ y ≤ z`,
`min (n.choose x) (n.choose z) ≤ n.choose y`. -/
theorem min_choose_le_choose {n x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    min (n.choose x) (n.choose z) ≤ n.choose y := by
  rcases le_or_gt y (n / 2) with hy | hy
  · exact (min_le_left _ _).trans (choose_le_choose_of_le_half hxy hy)
  · refine (min_le_right _ _).trans ?_
    rcases le_or_gt z n with hz | hz
    · rw [← Nat.choose_symm hz, ← Nat.choose_symm (hyz.trans hz)]
      exact choose_le_choose_of_le_half (by omega) (by omega)
    · rw [Nat.choose_eq_zero_of_lt hz]
      exact Nat.zero_le _

/-- **Layer-cake bound.** Let `w : ℕ → ℝ` have all its sums over `t` consecutive integers of
`[p, p + n)` at most `A + B t`, with `A ≥ 0`, and let `b` be quasi-concave on `[p, p + n)` with
values in `[0, M]`. Then `∑_{[p, p + n)} b w ≤ A M + B ∑_{[p, p + n)} b`. -/
theorem sum_Ico_mul_le_of_quasiConcave {A B : ℝ} (hA : 0 ≤ A) {w : ℕ → ℝ} (n : ℕ) :
    ∀ (p : ℕ) (b : ℕ → ℝ) (M : ℝ), 0 ≤ M →
    (∀ u t, p ≤ u → u + t ≤ p + n → ∑ k ∈ Ico u (u + t), w k ≤ A + B * t) →
    (∀ i j k, p ≤ i → i ≤ j → j ≤ k → k < p + n → min (b i) (b k) ≤ b j) →
    (∀ k, p ≤ k → k < p + n → 0 ≤ b k ∧ b k ≤ M) →
    ∑ k ∈ Ico p (p + n), b k * w k ≤ A * M + B * ∑ k ∈ Ico p (p + n), b k := by
  induction n with
  | zero =>
    intro p b M hM _ _ _
    simp only [add_zero, Ico_self, sum_empty, mul_zero, add_zero]
    positivity
  | succ n ih =>
    intro p b M hM hw hq hb
    set c := min (b p) (b (p + n)) with hc
    have hcle : ∀ k, p ≤ k → k < p + (n + 1) → c ≤ b k := fun k h1 h2 =>
      hq p k (p + n) le_rfl h1 (by omega) (by omega)
    have hc0 : 0 ≤ c := by
      rcases min_choice (b p) (b (p + n)) with h | h <;> rw [hc, h]
      · exact (hb p le_rfl (by omega)).1
      · exact (hb (p + n) (by omega) (by omega)).1
    have hcM : c ≤ M := (hcle p le_rfl (by omega)).trans (hb p le_rfl (by omega)).2
    have key : ∀ p', p ≤ p' → p' + n ≤ p + (n + 1) →
        (∀ k ∈ Ico p (p + (n + 1)), k ∉ Ico p' (p' + n) → b k - c = 0) →
        ∑ k ∈ Ico p (p + (n + 1)), b k * w k ≤
          A * M + B * ∑ k ∈ Ico p (p + (n + 1)), b k := by
      intro p' hp1 hp2 hout
      have hsub : Ico p' (p' + n) ⊆ Ico p (p + (n + 1)) := Ico_subset_Ico hp1 hp2
      have e1 : ∑ k ∈ Ico p (p + (n + 1)), (b k - c) * w k =
          ∑ k ∈ Ico p' (p' + n), (b k - c) * w k :=
        (sum_subset hsub fun k hk hk' => by rw [hout k hk hk', zero_mul]).symm
      have e2 : ∑ k ∈ Ico p (p + (n + 1)), (b k - c) = ∑ k ∈ Ico p' (p' + n), (b k - c) :=
        (sum_subset hsub fun k hk hk' => hout k hk hk').symm
      have hIH := ih p' (fun k => b k - c) (M - c) (sub_nonneg.2 hcM)
        (fun u t h1 h2 => hw u t (by omega) (by omega))
        (fun i j k h1 h2 h3 h4 => by
          simp only [min_sub_sub_right]
          exact sub_le_sub_right (hq i j k (by omega) h2 h3 (by omega)) c)
        (fun k h1 h2 => ⟨sub_nonneg.2 (hcle k (by omega) (by omega)),
          sub_le_sub_right (hb k (by omega) (by omega)).2 c⟩)
      have hW := hw p (n + 1) le_rfl le_rfl
      have e3 : ∑ k ∈ Ico p (p + (n + 1)), b k * w k =
          c * ∑ k ∈ Ico p (p + (n + 1)), w k + ∑ k ∈ Ico p (p + (n + 1)), (b k - c) * w k := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun k _ => by ring
      have e4 : ∑ k ∈ Ico p (p + (n + 1)), (b k - c) =
          ∑ k ∈ Ico p (p + (n + 1)), b k - c * (n + 1) := by
        rw [sum_sub_distrib, sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
        push_cast
        ring
      have hcW := mul_le_mul_of_nonneg_left hW hc0
      push_cast at hcW
      rw [← e2, e4] at hIH
      rw [e3, e1]
      nlinarith
    rcases min_choice (b p) (b (p + n)) with h | h
    · refine key (p + 1) (by omega) (by omega) fun k hk hk' => ?_
      simp only [mem_Ico] at hk hk'
      obtain rfl : k = p := by omega
      rw [hc, h, sub_self]
    · refine key p le_rfl (by omega) fun k hk hk' => ?_
      simp only [mem_Ico] at hk hk'
      obtain rfl : k = p + n := by omega
      rw [hc, h, sub_self]

/-- A finite set of integers in `[x, y]` whose distinct points are at distance at least `d` has
at most `1 + (y - x) / d` points: `(|s| - 1) d ≤ y - x`. -/
theorem card_sub_one_mul_le_of_separated {d : ℝ} (s : Finset ℤ) (hs : s.Nonempty)
    (hsep : ∀ z ∈ s, ∀ z' ∈ s, z ≠ z' → d ≤ |(z : ℝ) - z'|) {x : ℝ} :
    ∀ y : ℝ, (∀ z ∈ s, x ≤ z ∧ (z : ℝ) ≤ y) → ((s.card : ℝ) - 1) * d ≤ y - x := by
  induction s using Finset.induction_on_max with
  | empty => exact absurd hs (by simp)
  | insert a s has ih =>
    intro y hy
    have ha := hy a (mem_insert_self a s)
    have hnot : a ∉ s := fun h => lt_irrefl a (has a h)
    rw [card_insert_of_notMem hnot]
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp only [card_empty, zero_add, Nat.cast_one, sub_self, zero_mul, sub_nonneg]
      exact ha.1.trans ha.2
    · have hd : ∀ z ∈ s, (z : ℝ) ≤ a - d := by
        intro z hz
        have hlt : (z : ℝ) < a := by exact_mod_cast has z hz
        have := hsep a (mem_insert_self a s) z (mem_insert_of_mem hz) (has z hz).ne'
        rw [abs_of_pos (by linarith)] at this
        linarith
      have := ih hne (fun z hz z' hz' hzz' => hsep z (mem_insert_of_mem hz) z'
        (mem_insert_of_mem hz') hzz') (a - d)
        (fun z hz => ⟨(hy z (mem_insert_of_mem hz)).1, hd z hz⟩)
      push_cast
      linarith [ha.2]

/-- **Interval sums over separated blocks.** Let `g ≥ 0` be `L`-periodic with mean `μ` and
centred range `D`, let the distinct points of `Z ⊆ ℤ` be at distance at least `d₀ ≥ N ≥ 1`, and
let `V` be a set of integers each of the form `z + i` with `z ∈ Z`, `0 ≤ i < N`. Then the sum of
`g (k + a)` over the `k ∈ [u, u + t)` with `k ∈ V` is at most
`(1 + (N - 2) / d₀) (μ N + D) + (μ N + D) t / d₀`. -/
theorem sum_Ico_ite_mem_blocks_le {L : ℕ} (hL : 1 ≤ L) {g : ℕ → ℝ} (hg0 : ∀ k, 0 ≤ g k)
    (hg : ∀ k, g (k + L) = g k) {μ D : ℝ} (hμ : μ = (1 / L) * ∑ k ∈ range L, g k)
    (hD : D = (range (L + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)) -
      (range (L + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)))
    (a : ℕ) {N : ℕ} (hN : 1 ≤ N) {d₀ : ℝ} (hNd : (N : ℝ) ≤ d₀) {Z : Set ℤ}
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → d₀ ≤ |(z : ℝ) - z'|) (V : Finset ℤ)
    (hV : ∀ r ∈ V, ∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) (u t : ℕ) :
    ∑ k ∈ Ico u (u + t), (if (k : ℤ) ∈ V then g (k + a) else 0) ≤
      (1 + ((N : ℝ) - 2) / d₀) * (μ * N + D) + (μ * N + D) / d₀ * t := by
  classical
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd₀ : 0 < d₀ := by linarith
  set C := μ * N + D with hCdef
  have hμ0 : 0 ≤ μ := by
    rw [hμ]; exact mul_nonneg (by positivity) (sum_nonneg fun k _ => hg0 k)
  have hD0 : 0 ≤ D := by
    rw [hD, sub_nonneg]
    exact (inf'_le (fun k => ∑ j ∈ range k, (g j - μ)) (mem_range.2 (Nat.succ_pos L))).trans
      (le_sup' (fun k => ∑ j ∈ range k, (g j - μ)) (mem_range.2 (Nat.succ_pos L)))
  have hC : 0 ≤ C := by positivity
  set Z' := (Icc ((u : ℤ) - N + 1) (u + t - 1)).filter (· ∈ Z) with hZ'
  have hblock : ∀ z : ℤ, ∑ k ∈ Ico u (u + t),
      (if z ≤ (k : ℤ) ∧ (k : ℤ) < z + N then g (k + a) else 0) ≤ C := by
    intro z
    rw [← sum_filter]
    calc ∑ k ∈ (Ico u (u + t)).filter (fun k : ℕ => z ≤ (k : ℤ) ∧ (k : ℤ) < z + N), g (k + a)
        ≤ ∑ k ∈ Ico z.toNat (z.toNat + N), g (k + a) := by
          refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => hg0 _)
          simp only [mem_filter, mem_Ico] at hk ⊢
          omega
      _ = ∑ k ∈ Ico (z.toNat + a) (z.toNat + a + N), g k := by
          rw [sum_Ico_add', show z.toNat + N + a = z.toNat + a + N by omega]
      _ ≤ N * μ + D := sum_Ico_le_of_periodic hL hg hμ hD _ _
      _ = C := by rw [hCdef]; ring
  have hpt : ∀ k ∈ Ico u (u + t), (if (k : ℤ) ∈ V then g (k + a) else 0) ≤
      ∑ z ∈ Z', (if z ≤ (k : ℤ) ∧ (k : ℤ) < z + N then g (k + a) else 0) := by
    intro k hk
    have hnn : ∀ z ∈ Z', 0 ≤ (if z ≤ (k : ℤ) ∧ (k : ℤ) < z + N then g (k + a) else 0) :=
      fun z _ => by split_ifs <;> simp [hg0]
    split_ifs with hkV
    · obtain ⟨z, hz, i, hi, hki⟩ := hV _ hkV
      have hzZ' : z ∈ Z' := by
        simp only [hZ', mem_filter, mem_Icc, mem_Ico] at hk ⊢
        exact ⟨⟨by omega, by omega⟩, hz⟩
      refine le_trans (le_of_eq ?_) (single_le_sum hnn hzZ')
      rw [ite_eq_left (by omega)]
    · exact sum_nonneg hnn
  have hcard : (Z'.card : ℝ) ≤ 1 + ((t : ℝ) + N - 2) / d₀ := by
    rcases Z'.eq_empty_or_nonempty with h | hne
    · rw [h, card_empty, Nat.cast_zero, ← neg_le_iff_add_nonneg', le_div_iff₀ hd₀]
      have : (0 : ℝ) ≤ t := t.cast_nonneg
      linarith
    · have := card_sub_one_mul_le_of_separated Z' hne
        (fun z hz z' hz' h => hZ z (mem_filter.1 hz).2 z' (mem_filter.1 hz').2 h)
        (x := (u : ℝ) - N + 1) ((u : ℝ) + t - 1) (fun z hz => by
          simp only [hZ', mem_filter, mem_Icc] at hz
          constructor
          · have : ((u : ℤ) - N + 1 : ℤ) ≤ z := hz.1.1
            exact_mod_cast this
          · have : z ≤ ((u : ℤ) + t - 1 : ℤ) := hz.1.2
            exact_mod_cast this)
      have h2 : (Z'.card : ℝ) - 1 ≤ ((t : ℝ) + N - 2) / d₀ := by
        rw [le_div_iff₀ hd₀]; linarith
      linarith
  calc ∑ k ∈ Ico u (u + t), (if (k : ℤ) ∈ V then g (k + a) else 0)
      ≤ ∑ k ∈ Ico u (u + t), ∑ z ∈ Z',
          (if z ≤ (k : ℤ) ∧ (k : ℤ) < z + N then g (k + a) else 0) := sum_le_sum hpt
    _ = ∑ z ∈ Z', ∑ k ∈ Ico u (u + t),
          (if z ≤ (k : ℤ) ∧ (k : ℤ) < z + N then g (k + a) else 0) := sum_comm
    _ ≤ ∑ _z ∈ Z', C := sum_le_sum fun z _ => hblock z
    _ = Z'.card * C := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (1 + ((t : ℝ) + N - 2) / d₀) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = (1 + ((N : ℝ) - 2) / d₀) * C + C / d₀ * t := by field_simp; ring

/-- The row `k ↦ 𝖱(k - 1, l)` (with `k - 1` truncated) is bounded by `(2(3l - 1))^{-1/2}`. -/
theorem rawMass_pred_le_inv_sqrt {l : ℕ} (hl : 1 ≤ l) (k : ℕ) :
    rawMass (k - 1) l ≤ (√(2 * (3 * l - 1)))⁻¹ := by
  rcases Nat.eq_zero_or_pos (k - 1) with hk | hk
  · rw [hk, rawMass_zero, ite_eq_right (by omega)]
    positivity
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  rw [rawMass_eq_choose hk, show (((n + 1 : ℕ) : ℤ) - 1).toNat = n by omega, ← Real.sqrt_inv]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have h := choose_div_two_pow_sq_le n (2 * (k - 1) - 1)
  have e : (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) = 1 / 2 * (1 / 2 ^ n) := by
    rw [zpow_neg, zpow_natCast, pow_succ]; field_simp
  rw [e]
  calc (((n.choose (2 * (k - 1) - 1) : ℕ) : ℝ) * (1 / 2 * (1 / 2 ^ n))) ^ 2
      = 1 / 4 * (((n.choose (2 * (k - 1) - 1) : ℕ) : ℝ) / 2 ^ n) ^ 2 := by ring
    _ ≤ 1 / 4 * (2 / (3 * (n : ℝ) + 2)) := by gcongr
    _ = (2 * (3 * ((n + 1 : ℕ) : ℝ) - 1))⁻¹ := by
        rw [show 2 * (3 * ((n + 1 : ℕ) : ℝ) - 1) = 2 * (3 * n + 2) by push_cast; ring,
          mul_inv]
        ring

/-- The row `k ↦ 𝖱(k - 1, l)` is quasi-concave in `k`. -/
theorem min_rawMass_pred_le {l : ℕ} (hl : 1 ≤ l) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    min (rawMass (i - 1) l) (rawMass (k - 1) l) ≤ rawMass (j - 1) l := by
  rcases le_or_gt i 1 with hi | hi
  · rw [show i - 1 = 0 by omega, rawMass_zero, ite_eq_right (by omega)]
    exact (min_le_left _ _).trans (rawMass_nonneg _ _)
  rw [rawMass_eq_choose (by omega), rawMass_eq_choose (by omega), rawMass_eq_choose (by omega),
    ← min_mul_of_nonneg _ _ (by positivity)]
  gcongr
  have := min_choose_le_choose (n := ((l : ℤ) - 1).toNat)
    (show 2 * (i - 1) - 1 ≤ 2 * (j - 1) - 1 by omega)
    (show 2 * (j - 1) - 1 ≤ 2 * (k - 1) - 1 by omega)
  rw [← Nat.cast_min]
  exact_mod_cast this

/-- The row `k ↦ 𝖱(k - 1, l)` vanishes for `k ≥ l + 2`. -/
theorem rawMass_pred_eq_zero {l : ℕ} {k : ℕ} (hk : l + 2 ≤ k) : rawMass (k - 1) l = 0 := by
  rw [rawMass_eq_choose (show 1 ≤ k - 1 by omega), Nat.choose_eq_zero_of_lt
    (show ((l : ℤ) - 1).toNat < 2 * (k - 1) - 1 by omega), Nat.cast_zero, zero_mul]

/-- The row `k ↦ 𝖱(k - 1, l)` sums to at most `1/4` over `k < l + 2`. -/
theorem sum_range_rawMass_pred_le {l : ℕ} (hl : 2 ≤ l) :
    ∑ k ∈ range (l + 2), rawMass (k - 1) l ≤ 1 / 4 := by
  have hl0 : (l : ℤ) ≠ 0 := by omega
  rw [sum_range_succ', sum_range_succ']
  simp only [Nat.add_sub_cancel, Nat.zero_sub, rawMass_zero, ite_eq_right hl0, add_zero]
  exact sum_le_hasSum _ (fun k _ => rawMass_nonneg _ _)
    (hasSum_rawMass_succ (show (2 : ℤ) ≤ l by omega))

/-- **Packing against a renewal row** (finite form). Let `l ≥ 2`, `L ≥ 1`, `N ≥ 1`, `a ≥ 0`, let
`g : ℕ → ℝ` be nonnegative and `L`-periodic with mean `μ` over a period and with `D` the maximum
minus the minimum over `0 ≤ k ≤ L` of `∑_{j < k} (g j - μ)`. Let `d₀ ≥ N` and let the distinct
points of `Z ⊆ ℤ` be at distance at least `d₀`. Then for every finite set `S` of integers of the
form `z + i`, `z ∈ Z`, `0 ≤ i < N`,
`∑_{r ∈ S, r ≥ 1} 𝖱(r - 1, l) g(r + a) ≤
(μ N + D) ((1 + (N - 2) / d₀) / √(2(3l - 1)) + 1 / (4 d₀))`. -/
@[collatz_pos_dens "lem_c3_row_pack"]
theorem sum_rawMass_mul_periodic_le {l L N : ℕ} (hl : 2 ≤ l) (hL : 1 ≤ L) (hN : 1 ≤ N) (a : ℕ)
    {g : ℕ → ℝ} (hg0 : ∀ k, 0 ≤ g k) (hg : ∀ k, g (k + L) = g k) {μ D : ℝ}
    (hμ : μ = (1 / L) * ∑ k ∈ range L, g k)
    (hD : D = (range (L + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)) -
      (range (L + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)))
    {d₀ : ℝ} (hNd : (N : ℝ) ≤ d₀) {Z : Set ℤ}
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → d₀ ≤ |(z : ℝ) - z'|) (S : Finset ℤ)
    (hS : ∀ r ∈ S, ∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) :
    ∑ r ∈ S with 1 ≤ r, rawMass (r - 1).toNat l * g (r + a).toNat ≤
      (μ * N + D) * ((1 + ((N : ℝ) - 2) / d₀) * (1 / √(2 * (3 * l - 1))) + 1 / (4 * d₀)) := by
  have hd₀ : 0 < d₀ := lt_of_lt_of_le (by exact_mod_cast hN) hNd
  set C := μ * N + D with hCdef
  have hC : 0 ≤ C := by
    have hμ0 : 0 ≤ μ := by
      rw [hμ]; exact mul_nonneg (by positivity) (sum_nonneg fun k _ => hg0 k)
    have hD0 : 0 ≤ D := by
      rw [hD, sub_nonneg]
      exact (inf'_le (fun k => ∑ j ∈ range k, (g j - μ)) (mem_range.2 (Nat.succ_pos L))).trans
        (le_sup' (fun k => ∑ j ∈ range k, (g j - μ)) (mem_range.2 (Nat.succ_pos L)))
    positivity
  set b : ℕ → ℝ := fun k => rawMass (k - 1) l with hb
  set w : ℕ → ℝ := fun k => if (k : ℤ) ∈ S then g (k + a) else 0 with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => by simp only [hw]; split_ifs <;> simp [hg0]
  have e1 : ∑ r ∈ S with 1 ≤ r, rawMass (r - 1).toNat l * g (r + a).toNat =
      ∑ k ∈ (S.filter (1 ≤ ·)).image Int.toNat, b k * w k := by
    rw [sum_image (fun x hx y hy hxy => by
      simp only [coe_filter, Set.mem_ofPred_eq] at hx hy; omega)]
    refine sum_congr rfl fun r hr => ?_
    simp only [mem_filter] at hr
    simp only [hb, hw, show ((r.toNat : ℕ) : ℤ) = r by omega, ite_eq_left hr.1]
    congr 2 <;> omega
  have e2 : ∑ k ∈ (S.filter (1 ≤ ·)).image Int.toNat, b k * w k ≤
      ∑ k ∈ Ico 0 (0 + (l + 2)), b k * w k := by
    rw [← sum_filter_of_ne (p := fun k => k < l + 2) (fun k _ hk => by
      by_contra h
      exact hk (by simp only [hb, rawMass_pred_eq_zero (not_lt.1 h), zero_mul]))]
    refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_)
      (fun k _ _ => mul_nonneg (rawMass_nonneg _ _) (hw0 k))
    simp only [mem_filter] at hk
    simp only [mem_Ico]
    omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA0 : 0 ≤ 1 + ((N : ℝ) - 2) / d₀ := by
    rw [← neg_le_iff_add_nonneg', le_div_iff₀ hd₀]; linarith
  have hlayer := sum_Ico_mul_le_of_quasiConcave (A := (1 + ((N : ℝ) - 2) / d₀) * C) (B := C / d₀)
    (w := w) (mul_nonneg hA0 hC) (l + 2) 0 b (√(2 * (3 * l - 1)))⁻¹ (by positivity)
    (fun u t _ _ => sum_Ico_ite_mem_blocks_le hL hg0 hg hμ hD a hN hNd hZ S hS u t)
    (fun i j k _ hij hjk _ => min_rawMass_pred_le (by omega) hij hjk)
    (fun k _ _ => ⟨rawMass_nonneg _ _, rawMass_pred_le_inv_sqrt (by omega) k⟩)
  have hsum : ∑ k ∈ Ico 0 (0 + (l + 2)), b k ≤ 1 / 4 := by
    rw [zero_add, ← range_eq_Ico]; exact sum_range_rawMass_pred_le hl
  have hB : 0 ≤ C / d₀ := by positivity
  rw [e1]
  calc _ ≤ _ := e2
    _ ≤ _ := hlayer
    _ ≤ (1 + ((N : ℝ) - 2) / d₀) * C * (√(2 * (3 * l - 1)))⁻¹ + C / d₀ * (1 / 4) := by
        gcongr
    _ = C * ((1 + ((N : ℝ) - 2) / d₀) * (1 / √(2 * (3 * l - 1))) + 1 / (4 * d₀)) := by
        field_simp

/-- **Packing against a renewal row.** Under the hypotheses of `sum_rawMass_mul_periodic_le`,
with `V = {z + i : z ∈ Z, 0 ≤ i < N}`, the family `r ↦ 𝖱(r - 1, l) g(r + a)` over the `r ∈ V`
with `r ≥ 1` is summable, and its sum is at most
`(μ N + D) ((1 + (N - 2) / d₀) / √(2(3l - 1)) + 1 / (4 d₀))`. -/
@[collatz_pos_dens "lem_c3_row_pack"]
theorem tsum_rawMass_mul_periodic_le {l L N : ℕ} (hl : 2 ≤ l) (hL : 1 ≤ L) (hN : 1 ≤ N) (a : ℕ)
    {g : ℕ → ℝ} (hg0 : ∀ k, 0 ≤ g k) (hg : ∀ k, g (k + L) = g k) {μ D : ℝ}
    (hμ : μ = (1 / L) * ∑ k ∈ range L, g k)
    (hD : D = (range (L + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)) -
      (range (L + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)))
    {d₀ : ℝ} (hNd : (N : ℝ) ≤ d₀) {Z : Set ℤ}
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → d₀ ≤ |(z : ℝ) - z'|) :
    Summable (fun r : {r : ℤ // (∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r} =>
        rawMass ((r : ℤ) - 1).toNat l * g ((r : ℤ) + a).toNat) ∧
      ∑' r : {r : ℤ // (∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
        rawMass ((r : ℤ) - 1).toNat l * g ((r : ℤ) + a).toNat ≤
      (μ * N + D) * ((1 + ((N : ℝ) - 2) / d₀) * (1 / √(2 * (3 * l - 1))) + 1 / (4 * d₀)) := by
  have hf0 : 0 ≤ fun r : {r : ℤ // (∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r} =>
      rawMass ((r : ℤ) - 1).toNat l * g ((r : ℤ) + a).toNat :=
    fun r => mul_nonneg (rawMass_nonneg _ _) (hg0 _)
  have hfin : ∀ u : Finset {r : ℤ // (∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
      ∑ r ∈ u, rawMass ((r : ℤ) - 1).toNat l * g ((r : ℤ) + a).toNat ≤
        (μ * N + D) * ((1 + ((N : ℝ) - 2) / d₀) * (1 / √(2 * (3 * l - 1))) + 1 / (4 * d₀)) := by
    intro u
    have h := sum_rawMass_mul_periodic_le hl hL hN a hg0 hg hμ hD hNd hZ
      (u.map (Function.Embedding.subtype _)) (fun r hr => by
        obtain ⟨r', _, rfl⟩ := mem_map.1 hr
        exact r'.2.1)
    rwa [filter_true_of_mem (fun r hr => by
      obtain ⟨r', _, rfl⟩ := mem_map.1 hr
      exact r'.2.2), sum_map] at h
  exact ⟨summable_of_sum_le hf0 hfin, Real.tsum_le_of_sum_le hf0 hfin⟩

end CollatzPosDens
