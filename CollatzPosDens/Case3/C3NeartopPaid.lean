/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3Continuation
public import CollatzPosDens.Case3.C3EstarMass
public import CollatzPosDens.Case3.C3InitialMass
public import CollatzPosDens.Case3.C3PaidDom
public import CollatzPosDens.Case3.C3Near
public import CollatzPosDens.CharSum.ChBoundaryStep
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.FourierDecay.MoSerInverseMoment
public import CollatzPosDens.Renewal.RnHoldJmarginal
public import CollatzPosDens.Renewal.RnHorTailSharp
public import CollatzPosDens.StoppingTrace.TrFreshMarginal
public import CollatzPosDens.StoppingTrace.TrPassageAll
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Split

/-!
# Paid near-top contraction

Let `ι` be a Fourier parameter set, `J = ⌊n/2⌋`, let `ξ ∈ G_n` be a unit and form the renewal
function `Q` and the weighted supremum `Q_{m-1}` with threshold `ε_*` and a real exponent
`0 ≤ A ≤ A_*(ι)`. For an integer `m ≥ 2^{42}` and a black point `e ∈ 𝒫` with `j(e) + m = J` and
gap `ω = gap(e) ≤ ς(ι, m)`,
$$Q(e) \le \tfrac{1999}{2000}\, m^{-A}\, Q_{m-1}.$$

Here `A_*(o) = 21193/10000 ≤ 11/5`, `A_*(b) = 17/10`, `ς(o, m) = 3m/2` and `ς(b, m) = 2m`, so
`0 ≤ A ≤ 3` and `ω ≤ 2m` for both indices.

Continuing through one hold, `Q(e) ≤ ∑_a μ̃_e(a) Q(y^e_1(a))` over the atoms
`a = ((r, ℓ), β)` of the paid fresh law. An atom of nonzero mass has `r ≥ 1`, and its path
reaches `j(y^e_1(a)) = j(e) + r + j(β¹)`, so `CollatzPosDens.chQ_le_boundary_step` gives
`Q(y^e_1(a)) ≤ max(m - r - j(β¹), 1)^{-A} Q_{m-1}`. Hence `Q(e) ≤ m^{-A} Q_{m-1} Z` with
`Z = ∑_a μ̃_e(a) θ(a)^A`, `θ(a) = m / max(m - r - j(β¹), 1) ∈ [1, m]`. Put `u = m/4096`.

* On the atoms with `r > ω/4 + u` or `j(β¹) > u`, `θ^A ≤ θ^3 ≤ m³` and `μ̃_e ≤ μ_{e,ω}`; the
  sharp horizontal tail of `F_ω` and the geometric tail of the first block bound their fresh mass
  by `7 e^{-m/2^{26}}`, and `e^y ≥ y^{11}/11!` at `y = m/2^{26} ≥ 2^{16}` gives
  `8 m³ e^{-m/2^{26}} < 2^{-20}`.
* On the remaining atoms with `ω ≥ 2^{34}` the paid mass is below `q_mass = 38177/125000`. For
  `ι = o`, `ω ≤ 3m/2` gives `θ ≤ 2048/1279`, and the exact comparison
  `(38177 · 1000)^5 · 2048^{11} < (125000 · 999)^5 · 1279^{11}` gives a contribution below
  `999/1000`; for `ι = b`, `ω ≤ 2m` gives `θ ≤ 2048/1023`, and
  `(38177 · 1000)^{10} · 2048^{17} < (125000 · 999)^{10} · 1023^{17}` does the same.
* On the remaining atoms with `ω < 2^{34}`, `ω/4 < m/1024`, so `θ ≤ 2048/2045`, and the paid
  mass is at most `96338641/10^8` by
  `CollatzPosDens.tsum_trPassage_mul_exp_neg_trCount_le_of_bkBlack`; the comparisons
  `96338641^5 · 2048^{11} < (97 · 10^6)^5 · 2045^{11}` (for `o`) and
  `96338641^{10} · 2048^{17} < (97 · 10^6)^{10} · 2045^{17}` (for `b`) give a contribution below
  `97/100`.

So `Z < 999/1000 + 2^{-20} < 1999/2000`.

## Main results

* `CollatzPosDens.chQ_le_mul_rpow_neg_chQm_of_trGap_le`: the paid near-top contraction.

## Implementation notes

The hypothesis `n ≥ 1` is omitted, since it follows from `j(e) + m = J` with `j(e) ≥ 1`. The point
`e` is taken in `𝒫` with `BkBlack` for `(n, ξ, ε_*)`, and `j(e) + m = J` is an identity in `ℤ`. The
sums over atoms are taken in `[0, ∞]`, as in `CollatzPosDens.chQ_le_tsum_trFreshLaw_mul_exp`. The
first-block tail `(11/16)^{⌊u⌋}` is bounded by `e^{-5u/32}` (from `11/16 ≤ e^{-5/16}`, which is
`1 + x ≤ e^x` at `x = -5/16`, and `⌊u⌋ ≥ u/2` for `u ≥ 2`) in place of `(16/11) e^{-5u/16}`, so the
exceptional mass is below `7 e^{-m/2^{26}}` rather than `8 e^{-m/2^{26}}`. The numerical gates are
verified by `norm_num` on the rational inequalities, which are equivalent to the integer
comparisons above.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

open Real

/-- **The horizontal tail.** For `m ≥ 2^{42}`, `ω ≤ 2m` and `u = m/4096`, the first-passage
law `F_ω` puts mass at most `6 e^{-m/2^{26}}` on the displacements `(r, ℓ)` with
`r > ω/4 + u`. -/
private lemma c3NeartopPaid_hor_tail {ω m : ℕ} (hm : 2 ^ 42 ≤ m) (hωm : ω ≤ 2 * m) :
    ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw ω ((rl.1 : ℤ), rl.2)) *
        (if (ω : ℝ) / 4 + m / 4096 < rl.1 then 1 else 0) ≤
      ENNReal.ofReal (6 * exp (-((m : ℝ) / 2 ^ 26))) := by
  set u : ℝ := m / 4096 with hu
  have hmr : (2 : ℝ) ^ 42 ≤ m := by exact_mod_cast hm
  have hu2 : 2 ≤ u := by rw [hu]; linarith
  set S : Set ℤ := {r | u ≤ |(r : ℝ) - ω / 4|} with hS
  set F : ℤ × ℤ → ℝ := fun x ↦ firstPassageLaw ω x with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x ↦ firstPassageLaw_nonneg _ _
  have hsum : Summable fun r : S ↦ ∑' ℓ : ℤ, F ((r : ℤ), ℓ) :=
    (summable_firstPassageLaw ω).prod.subtype S
  have hreal : ∑' r : S, ∑' ℓ : ℤ, F ((r : ℤ), ℓ) ≤ 6 * exp (-((m : ℝ) / 2 ^ 26)) := by
    have hx : exp (-(u / 256)) ≤ exp (-((m : ℝ) / 2 ^ 26)) :=
      exp_le_exp.2 (by rw [hu]; have : (0 : ℝ) ≤ m := by positivity
                       linarith)
    have hx0 := exp_pos (-((m : ℝ) / 2 ^ 26))
    rcases le_or_gt ω 5 with h5 | h6
    · have := tsum_firstPassageLaw_hor_tail_le_of_le_five h5 hu2
      exact this.trans (by linarith)
    · have := tsum_firstPassageLaw_hor_tail_le_of_six_le (s := ω) (by omega) hu2
      refine this.trans ?_
      have hω6 : (6 : ℝ) ≤ ω := by exact_mod_cast h6
      have hωm' : (ω : ℝ) ≤ 2 * m := by exact_mod_cast hωm
      have hpos : (0 : ℝ) < 2 * ((ω : ℝ) - 4) := by linarith
      have hq : (m : ℝ) / 2 ^ 26 ≤ u ^ 2 / (2 * ((ω : ℝ) - 4)) := by
        rw [le_div_iff₀ hpos, hu]
        have : (0 : ℝ) ≤ m := by positivity
        nlinarith
      have hy : exp (-(u ^ 2 / (2 * ((ω : ℝ) - 4)))) ≤ exp (-((m : ℝ) / 2 ^ 26)) :=
        exp_le_exp.2 (by linarith)
      linarith
  have hind : ∀ r : ℤ, ∑' ℓ : ℤ, (if u ≤ |(r : ℝ) - ω / 4| then ENNReal.ofReal (F (r, ℓ))
      else 0) = S.indicator (fun r ↦ ∑' ℓ : ℤ, ENNReal.ofReal (F (r, ℓ))) r := by
    intro r
    by_cases hr : u ≤ |(r : ℝ) - ω / 4|
    · simp [hr, hS]
    · simp [hr, hS]
  calc _ ≤ ∑' rl : ℕ × ℤ, (fun p : ℤ × ℤ ↦ if u ≤ |(p.1 : ℝ) - ω / 4| then
          ENNReal.ofReal (F p) else 0) ((rl.1 : ℤ), rl.2) := by
        refine ENNReal.tsum_le_tsum fun rl ↦ ?_
        by_cases h : (ω : ℝ) / 4 + u < rl.1
        · have h' : u ≤ |((rl.1 : ℤ) : ℝ) - ω / 4| := by
            rw [Int.cast_natCast]
            exact (by linarith : u ≤ (rl.1 : ℝ) - ω / 4).trans (le_abs_self _)
          rw [ite_eq_left h, mul_one]
          exact (ite_eq_left h').symm.le
        · simp [h]
    _ ≤ ∑' p : ℤ × ℤ, (if u ≤ |(p.1 : ℝ) - ω / 4| then ENNReal.ofReal (F p) else 0) :=
        ENNReal.tsum_comp_le_tsum_of_injective natCast_prod_injective
          (fun p : ℤ × ℤ ↦ if u ≤ |(p.1 : ℝ) - ω / 4| then ENNReal.ofReal (F p) else 0)
    _ = ∑' r : ℤ, S.indicator (fun r ↦ ∑' ℓ : ℤ, ENNReal.ofReal (F (r, ℓ))) r := by
        rw [ENNReal.tsum_prod']
        exact tsum_congr hind
    _ = ∑' r : S, ∑' ℓ : ℤ, ENNReal.ofReal (F ((r : ℤ), ℓ)) := (tsum_subtype S _).symm
    _ = ∑' r : S, ENNReal.ofReal (∑' ℓ : ℤ, F ((r : ℤ), ℓ)) := by
        refine tsum_congr fun r ↦ ?_
        exact (ENNReal.ofReal_tsum_of_nonneg (fun ℓ ↦ hF0 _)
          ((summable_firstPassageLaw ω).prod_factor r)).symm
    _ = ENNReal.ofReal (∑' r : S, ∑' ℓ : ℤ, F ((r : ℤ), ℓ)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun r ↦ tsum_nonneg fun ℓ ↦ hF0 _) hsum).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- **The tail of the first block.** For real `u ≥ 2`, the holding law puts mass at most
`e^{-5u/32}` on the block points `h ∈ 𝒫` with `j(h) > u`: this mass is the geometric tail
`∑_{j > u} ν₄₅(j) = (11/16)^{⌊u⌋}`, and `11/16 ≤ e^{-5/16}`. -/
private lemma c3NeartopPaid_hold_tail {u : ℝ} (hu : 2 ≤ u) :
    ∑' h : {h : Fin 1 → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        ENNReal.ofReal (holdListLaw fun i ↦ ((h.1 i).1.toNat, (h.1 i).2)) *
          (if u < ((bkJ (h.1 0) : ℤ) : ℝ) then 1 else 0) ≤
      ENNReal.ofReal (exp (-(5 * u / 32))) := by
  set K := ⌊u⌋₊ with hK
  have hu0 : 0 ≤ u := by linarith
  have hKu : u < K + 1 := Nat.lt_floor_add_one u
  calc _ ≤ ∑' h : {h : Fin 1 → ℤ × ℤ // ∀ i, h i ∈ bkPoints},
        (fun p : ℕ × ℤ ↦ if u < (p.1 : ℝ) then ENNReal.ofReal (holdLaw p.1 p.2) else 0)
          (((h.1 0).1.toNat, (h.1 0).2)) := by
        refine ENNReal.tsum_le_tsum fun h ↦ ?_
        have h0 := mem_bkPoints.1 (h.2 0)
        have hc : (((h.1 0).1.toNat : ℕ) : ℝ) = ((bkJ (h.1 0) : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by simp only [bkJ] at h0; omega)]
        rw [holdListLaw_one]
        dsimp only
        rw [hc]
        split_ifs <;> simp
    _ ≤ ∑' p : ℕ × ℤ, (if u < (p.1 : ℝ) then ENNReal.ofReal (holdLaw p.1 p.2) else 0) := by
        refine ENNReal.tsum_comp_le_tsum_of_injective (fun h h' hh ↦ ?_)
          (fun p : ℕ × ℤ ↦ if u < (p.1 : ℝ) then ENNReal.ofReal (holdLaw p.1 p.2) else 0)
        simp only [Prod.mk.injEq] at hh
        have h0 := mem_bkPoints.1 (h.2 0)
        have h0' := mem_bkPoints.1 (h'.2 0)
        simp only [bkJ] at h0 h0'
        refine Subtype.ext (funext fun i ↦ ?_)
        rw [Subsingleton.elim i 0]
        exact Prod.ext (by omega) hh.2
    _ = ∑' j : ℕ, (if u < (j : ℝ) then ENNReal.ofReal (nu45 j) else 0) := by
        rw [ENNReal.tsum_prod']
        refine tsum_congr fun j ↦ ?_
        by_cases hj : u < (j : ℝ)
        · have hj1 : 1 ≤ j := by
            have : (1 : ℝ) < j := by linarith
            exact_mod_cast this.le
          simp only [hj, ite_true]
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun l ↦ holdLaw_nonneg _ _)
            (hasSum_holdLaw hj1).summable, tsum_holdLaw hj1]
        · simp [hj]
    _ = ∑' r : ℕ, (if u < ((r : ℝ) + 1) then ENNReal.ofReal (nu45 ((r : ℤ) + 1)) else 0) := by
        rw [tsum_eq_zero_add' ENNReal.summable]
        have h0 : ¬ u < ((0 : ℕ) : ℝ) := by simp only [Nat.cast_zero, not_lt]; exact hu0
        simp only [h0, ite_false, zero_add]
        refine tsum_congr fun r ↦ ?_
        push_cast
        rfl
    _ ≤ ∑' r : ℕ, ENNReal.ofReal (if K ≤ r then nu45 ((r : ℤ) + 1) else 0) := by
        refine ENNReal.tsum_le_tsum fun r ↦ ?_
        by_cases hr : u < (r : ℝ) + 1
        · have hKr : K ≤ r := by
            have : K < r + 1 := (Nat.floor_lt hu0).2 (by exact_mod_cast hr)
            omega
          simp [hr, hKr]
        · simp [hr]
    _ = ENNReal.ofReal ((11 / 16 : ℝ) ^ K) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun r ↦ by split_ifs <;> simp [nu45_nonneg])
          (hasSum_nu45_tail K).summable, (hasSum_nu45_tail K).tsum_eq]
    _ ≤ ENNReal.ofReal (exp (-(5 * u / 32))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (11 / 16 : ℝ) ≤ exp (-(5 / 16)) := by
          have := add_one_le_exp (-(5 / 16 : ℝ))
          linarith
        calc (11 / 16 : ℝ) ^ K ≤ exp (-(5 / 16)) ^ K := pow_le_pow_left₀ (by norm_num) h1 K
          _ = exp (K * (-(5 / 16))) := (exp_nat_mul _ K).symm
          _ ≤ exp (-(5 * u / 32)) := exp_le_exp.2 (by nlinarith)

/-- The numerical smallness of the exceptional atoms: `8 m³ e^{-m/2^{26}} < 2^{-20}` for
`m ≥ 2^{42}`, from `e^y ≥ y^{11}/11!` at `y = m/2^{26} ≥ 2^{16}` and `8 · 11! < 2^{30}`. -/
private lemma c3NeartopPaid_small {m : ℝ} (hm : 2 ^ 42 ≤ m) :
    8 * m ^ 3 * exp (-(m / 2 ^ 26)) < 1 / 2 ^ 20 := by
  set x := m / 2 ^ 26 with hx
  have hx16 : (2 : ℝ) ^ 16 ≤ x := by rw [hx, le_div_iff₀ (by positivity)]; linarith
  have hmx : m = 2 ^ 26 * x := by rw [hx]; ring
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx16
  have he := pow_div_factorial_le_exp x hx0.le 11
  have h8 : ((2 : ℝ) ^ 16) ^ 8 ≤ x ^ 8 := pow_le_pow_left₀ (by positivity) hx16 8
  have hfac : ((Nat.factorial 11 : ℕ) : ℝ) = 39916800 := by norm_num [Nat.factorial]
  rw [hfac] at he
  have hx3 : 0 < x ^ 3 := by positivity
  have hkey : 8 * m ^ 3 * 2 ^ 20 < x ^ 11 / 39916800 := by
    rw [hmx, lt_div_iff₀ (by norm_num)]
    have h11 : x ^ 11 = x ^ 3 * x ^ 8 := by ring
    have hc : (8 * (2 : ℝ) ^ 78 * 2 ^ 20 * 39916800) < ((2 : ℝ) ^ 16) ^ 8 := by norm_num
    rw [h11]
    have := mul_le_mul_of_nonneg_left h8 hx3.le
    have := mul_lt_mul_of_pos_left hc hx3
    nlinarith
  have hE := exp_pos (-x)
  rw [lt_div_iff₀ (by positivity)]
  calc 8 * m ^ 3 * exp (-x) * 2 ^ 20 = 8 * m ^ 3 * 2 ^ 20 * exp (-x) := by ring
    _ < x ^ 11 / 39916800 * exp (-x) := mul_lt_mul_of_pos_right hkey hE
    _ ≤ exp x * exp (-x) := mul_le_mul_of_nonneg_right he hE.le
    _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

/-- Raising to the `k`-th power: if `p k = j` and `M^k c^j < B^k` then `M c^p < B`. -/
private lemma c3NeartopPaid_gate {M c B p : ℝ} {k j : ℕ} (hk : k ≠ 0) (hp : p * k = j)
    (hM : 0 ≤ M) (hc : 0 ≤ c) (hB : 0 ≤ B) (h : M ^ k * c ^ j < B ^ k) : M * c ^ p < B := by
  have hpow : (M * c ^ p) ^ k = M ^ k * c ^ j := by
    rw [mul_pow, ← rpow_natCast (c ^ p), ← rpow_mul hc, hp, rpow_natCast]
  rw [← pow_lt_pow_iff_left₀ (by positivity) hB hk, hpow]
  exact h

/-- The paid fresh law has total mass at most that of the paid passage mass. -/
private lemma c3NeartopPaid_tsum_c3PaidLaw_le (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) :
    ∑' a : trAtoms n, c3PaidLaw n ξ e a ≤ ∑' x : ℤ × ℤ, c3PaidPassage n ξ e x := by
  rw [← (trAtomsEquiv n).symm.tsum_eq, ENNReal.tsum_prod']
  refine (ENNReal.tsum_le_tsum fun rl ↦ le_of_eq ?_).trans
    (ENNReal.tsum_comp_le_tsum_of_injective natCast_prod_injective (c3PaidPassage n ξ e))
  simp only [trAtomsEquiv, Equiv.coe_fn_symm_mk, c3PaidLaw_def]
  rw [ENNReal.tsum_mul_left, tsum_ofReal_trListWeight_length_eq, mul_one]

/-- The fresh law of the event `j(β¹) > u` is at most `e^{-5u/32}`. -/
private lemma c3NeartopPaid_tsum_trFreshLaw_hold (n : ℕ) (e : ℤ × ℤ) (g : ℕ) (hJ : 1 ≤ n / 2)
    {u : ℝ} (hu : 2 ≤ u) :
    ∑' a : trAtoms n, ENNReal.ofReal (trFreshLaw n e g a) *
        (if u < ((((a.1.2.take 1).map fun b ↦ bkJ (chBlockPoint b)).sum : ℤ) : ℝ) then 1
          else 0) ≤
      ENNReal.ofReal (exp (-(5 * u / 32))) := by
  have key := tsum_trFreshLaw_mul_chBlockPoint n e g 1 hJ
    (fun _ h ↦ if u < ((bkJ (h 0) : ℤ) : ℝ) then 1 else 0)
  calc _ = ∑' a : trAtoms n, ENNReal.ofReal (trFreshLaw n e g a) *
        (fun (_ : ℕ × ℤ) (h : Fin 1 → ℤ × ℤ) ↦ if u < ((bkJ (h 0) : ℤ) : ℝ) then
          (1 : ℝ≥0∞) else 0) a.1.1 (fun i ↦ chBlockPoint (a.1.2[(i : ℕ)]'(by
            have := (mem_trAtoms.1 a.2).1; omega))) := by
        refine tsum_congr fun a ↦ ?_
        obtain ⟨⟨rl, β⟩, ha⟩ := a
        have hlen : β.length = n / 2 := ha.1
        obtain ⟨b, β', rfl⟩ : ∃ b β', β = b :: β' := by
          cases β with
          | nil => simp at hlen; omega
          | cons b β' => exact ⟨b, β', rfl⟩
        simp
    _ = _ := key
    _ ≤ ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) *
          ENNReal.ofReal (exp (-(5 * u / 32))) :=
        ENNReal.tsum_le_tsum fun rl ↦ mul_le_mul_right (c3NeartopPaid_hold_tail hu) _
    _ ≤ ENNReal.ofReal (exp (-(5 * u / 32))) := by
        rw [ENNReal.tsum_mul_right]
        exact (mul_le_mul_left (tsum_ofReal_firstPassageLaw_natCast_le_one g) _).trans_eq
          (one_mul _)

/-- The bound for a single atom after continuing through one hold, for an exponent `A ≤ B ≤ 3`:
a main atom contributes at most `c₀^B` times its paid mass, an exceptional one at most `m³` times
its fresh mass. -/
private lemma c3NeartopPaid_atom {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ} (he : e ∈ bkPoints)
    {A : ℝ} (hA₀ : 0 ≤ A) {B : ℝ} (hAB : A ≤ B) (hB : B ≤ 3) {m : ℕ} (hm : 1 ≤ m)
    (hjm : bkJ e + m = ((n / 2 : ℕ) : ℤ)) {ω : ℕ} (hωZ : (ω : ℤ) = trGap n ξ (epsStar : ℝ) e)
    {u c₀ : ℝ}
    (hG : ∀ r U : ℕ, (r : ℝ) ≤ ω / 4 + u → (U : ℝ) ≤ u →
      (m : ℝ) ≤ c₀ * ((max ((m : ℤ) - ((r + U : ℕ) : ℤ)) 1 : ℤ) : ℝ))
    (a : trAtoms n) :
    c3PaidLaw n ξ e a * ENNReal.ofReal (Real.exp (-(zStar : ℝ) * trWhiteCount n ξ e a (1 - 1)) *
        chQ n ξ (epsStar : ℝ) (trFreshPath e a 1)) ≤
      ENNReal.ofReal ((m : ℝ) ^ (-A) * chQm n ξ (epsStar : ℝ) A (m - 1)) *
        (ENNReal.ofReal (c₀ ^ B) * c3PaidLaw n ξ e a +
          ENNReal.ofReal ((m : ℝ) ^ 3) *
            (ENNReal.ofReal (trFreshLaw n e ω a) *
                (if (ω : ℝ) / 4 + u < (a.1.1.1 : ℝ) then 1 else 0) +
              ENNReal.ofReal (trFreshLaw n e ω a) *
                (if u < ((((a.1.2.take 1).map fun b ↦ bkJ (chBlockPoint b)).sum : ℤ) : ℝ) then 1
                  else 0))) := by
  obtain ⟨⟨⟨r, ℓ⟩, β⟩, ha⟩ := a
  simp only
  set P := c3PaidLaw n ξ e ((r, ℓ), β) with hP
  by_cases hP0 : P = 0
  · rw [hP0, zero_mul]
    exact zero_le
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | h
    · exact absurd (c3PaidLaw_zero_left ℓ β) hP0
    · exact h
  set Uz : ℤ := ((β.take 1).map fun b ↦ bkJ (chBlockPoint b)).sum with hUz
  have hU0 : 0 ≤ Uz := List.sum_nonneg fun x hx ↦ by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
    exact bkJ_chBlockPoint_nonneg b
  set U := Uz.toNat with hU
  have hUU : (U : ℤ) = Uz := Int.toNat_of_nonneg hU0
  have hy := bkJ_trFreshPath e r ℓ β 1
  rw [← hUz] at hy
  have hyP : trFreshPath e ((r, ℓ), β) 1 ∈ bkPoints := by
    rw [mem_bkPoints, hy]
    have := mem_bkPoints.1 he
    omega
  have hstep := chQ_le_boundary_step n ξ (epsStar : ℝ) hA₀ (m := m) (r := r + U) (by omega) hyP
    (by rw [hy]; push_cast; omega)
  set D : ℤ := max ((m : ℤ) - ((r + U : ℕ) : ℤ)) 1 with hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast le_max_right _ _
  have hDm : (D : ℝ) ≤ m := by
    have : D ≤ m := max_le (by omega) (by exact_mod_cast hm)
    exact_mod_cast this
  have hD0 : (0 : ℝ) < D := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set Qm := chQm n ξ (epsStar : ℝ) A (m - 1) with hQm
  have hQm0 : 0 ≤ Qm := chQm_nonneg _ _ _ _ _
  set θ : ℝ := (m : ℝ) / D with hθ
  have hθ1 : 1 ≤ θ := by rw [hθ, le_div_iff₀ hD0]; linarith
  have hθm : θ ≤ m := by rw [hθ, div_le_iff₀ hD0]; nlinarith
  have hDA : (D : ℝ) ^ (-A) = (m : ℝ) ^ (-A) * θ ^ A := by
    rw [hθ, div_rpow hm0.le hD0.le, rpow_neg hm0.le, rpow_neg hD0.le]
    field_simp [(rpow_pos_of_pos hm0 A).ne']
  have hK0 : 0 ≤ (m : ℝ) ^ (-A) * Qm := mul_nonneg (rpow_nonneg hm0.le _) hQm0
  have hterm : ENNReal.ofReal (Real.exp (-(zStar : ℝ) *
        trWhiteCount n ξ e ((r, ℓ), β) (1 - 1)) *
          chQ n ξ (epsStar : ℝ) (trFreshPath e ((r, ℓ), β) 1)) ≤
      ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm) * ENNReal.ofReal (θ ^ A) := by
    rw [Nat.sub_self, trWhiteCount_zero, mul_zero, exp_zero, one_mul,
      ← ENNReal.ofReal_mul hK0]
    refine ENNReal.ofReal_le_ofReal (hstep.trans_eq ?_)
    rw [hDA]
    ring
  have hθA0 : 0 ≤ θ ^ A := rpow_nonneg (by linarith) A
  by_cases hgood : r ≤ (ω : ℝ) / 4 + u ∧ (U : ℝ) ≤ u
  · have hθc : θ ≤ c₀ := by
      rw [hθ, div_le_iff₀ hD0]
      exact hG r U hgood.1 hgood.2
    have hθA : θ ^ A ≤ c₀ ^ B :=
      (rpow_le_rpow_of_exponent_le hθ1 hAB).trans
        (rpow_le_rpow (by linarith) hθc (by linarith))
    calc P * _ ≤ P * (ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm) * ENNReal.ofReal (c₀ ^ B)) :=
          mul_le_mul_right (hterm.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hθA) _)) _
      _ = ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm) * (ENNReal.ofReal (c₀ ^ B) * P) := by
          ring
      _ ≤ _ := mul_le_mul_right le_self_add _
  · have hθA : θ ^ A ≤ (m : ℝ) ^ 3 := by
      calc θ ^ A ≤ θ ^ ((3 : ℕ) : ℝ) := rpow_le_rpow_of_exponent_le hθ1 (by push_cast; linarith)
        _ = θ ^ 3 := rpow_natCast θ 3
        _ ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hθm 3
    have hPF : P ≤ ENNReal.ofReal (trFreshLaw n e ω ((r, ℓ), β)) := by
      rw [hP, c3PaidLaw_mk, trFreshLaw_mk, ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _)]
      refine mul_le_mul_left ?_ _
      have := (c3PaidPassage_le_firstPassageLaw n ξ e ((r : ℤ), ℓ)).2
      rwa [← hωZ] at this
    have hind : (1 : ℝ≥0∞) ≤ (if (ω : ℝ) / 4 + u < (r : ℝ) then 1 else 0) +
        (if u < ((Uz : ℤ) : ℝ) then 1 else 0) := by
      have hUr : ((Uz : ℤ) : ℝ) = (U : ℝ) := by rw [← hUU]; rfl
      rw [hUr]
      rw [not_and_or, not_le, not_le] at hgood
      rcases hgood with h | h
      · simp [h]
      · simp [h]
    set F := ENNReal.ofReal (trFreshLaw n e ω ((r, ℓ), β))
    calc P * _ ≤ F * (ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm) * ENNReal.ofReal ((m : ℝ) ^ 3)) :=
          mul_le_mul' hPF (hterm.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hθA) _))
      _ ≤ F * (ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm) * ENNReal.ofReal ((m : ℝ) ^ 3)) *
          ((if (ω : ℝ) / 4 + u < (r : ℝ) then 1 else 0) +
            (if u < ((Uz : ℤ) : ℝ) then 1 else 0)) := le_mul_of_one_le_right zero_le hind
      _ = ENNReal.ofReal ((m : ℝ) ^ (-A) * Qm) * (ENNReal.ofReal ((m : ℝ) ^ 3) *
          (F * (if (ω : ℝ) / 4 + u < (r : ℝ) then 1 else 0) +
            F * (if u < ((Uz : ℤ) : ℝ) then 1 else 0))) := by ring
      _ ≤ _ := mul_le_mul_right le_add_self _

/-- **Paid near-top contraction.** Let `ι` be a Fourier parameter set, `ξ ∈ G_n` a unit, `A`
real with `0 ≤ A ≤ A_*(ι)`, and let `Q` and `Q_{m-1}` be formed with `ε = ε_*` and exponent `A`.
Let `m ≥ 2^{42}` be an integer and `e ∈ 𝒫` black with `j(e) + m = ⌊n/2⌋` and
`gap(e) ≤ ς(ι, m)`. Then `Q(e) ≤ (1999/2000) m^{-A} Q_{m-1}`. -/
@[collatz_pos_dens "lem_c3_neartop_paid"]
theorem chQ_le_mul_rpow_neg_chQm_of_trGap_le (ι : FIndex) {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {A : ℝ} (hA₀ : 0 ≤ A) (hA : A ≤ (Aexp ι : ℝ)) {m : ℕ}
    (hm : 2 ^ 42 ≤ m) {e : ℤ × ℤ} (he : e ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) e)
    (hjm : bkJ e + m = ((n / 2 : ℕ) : ℤ))
    (hgap : ((trGap n ξ (epsStar : ℝ) e : ℤ) : ℝ) ≤ gapSplit ι m) :
    chQ n ξ (epsStar : ℝ) e ≤
      1999 / 2000 * (m : ℝ) ^ (-A) * chQm n ξ (epsStar : ℝ) A (m - 1) := by
  have he1 := mem_bkPoints.1 he
  have hJ : 1 ≤ n / 2 := by omega
  have hω0 : 0 ≤ trGap n ξ (epsStar : ℝ) e := trGap_nonneg _ _ _ _
  set ω := (trGap n ξ (epsStar : ℝ) e).toNat with hωdef
  have hωZ : (ω : ℤ) = trGap n ξ (epsStar : ℝ) e := Int.toNat_of_nonneg hω0
  have hmr : (2 : ℝ) ^ 42 ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hωR : (ω : ℝ) ≤ gapSplit ι m := by
    rw [← hωZ] at hgap
    exact_mod_cast hgap
  have hω2 : (ω : ℝ) ≤ 2 * m := by
    cases ι with
    | o => rw [gapSplit_o] at hωR; linarith
    | b => rw [gapSplit_b] at hωR; linarith
  have hωm : ω ≤ 2 * m := by exact_mod_cast hω2
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  set u : ℝ := m / 4096 with hu
  have hu2 : 2 ≤ u := by rw [hu]; linarith
  set Qm := chQm n ξ (epsStar : ℝ) A (m - 1) with hQm
  have hQm0 : 0 ≤ Qm := chQm_nonneg _ _ _ _ _
  set K : ℝ := (m : ℝ) ^ (-A) * Qm with hK
  have hK0 : 0 ≤ K := mul_nonneg (rpow_nonneg (by positivity) _) hQm0
  set M := ∑' a : trAtoms n, c3PaidLaw n ξ e a with hM
  have hML : 2 ^ 34 ≤ ω → M ≤ ENNReal.ofReal (38177 / 125000) := fun h34 ↦
    (c3NeartopPaid_tsum_c3PaidLaw_le n ξ e).trans
      ((tsum_c3PaidPassage_lt_qMass hξ he hb (by rw [← hωZ]; exact_mod_cast h34)).le.trans_eq
        (by rw [qMass_cast]))
  have hMS : ω < 2 ^ 34 → M ≤ ENNReal.ofReal (96338641 / 10 ^ 8) := fun _ ↦ by
    have hsum := summable_trPassage_mul_exp_neg_trCount ξ e ω
    have hall := tsum_trPassage_mul_exp_neg_trCount_le_of_bkBlack hξ he hb
    rw [← hωdef] at hall
    have hz : (gammaStar : ℝ) = zStar := by rw [gammaStar_cast, zStar_cast]
    rw [hz] at hsum hall
    refine (c3NeartopPaid_tsum_c3PaidLaw_le n ξ e).trans ?_
    rw [tsum_c3PaidPassage_eq, ← hωdef, ← ENNReal.ofReal_tsum_of_nonneg
      (fun p ↦ mul_nonneg (trListWeight_nonneg _) (exp_pos _).le) hsum]
    exact ENNReal.ofReal_le_ofReal hall
  have hfin : ∀ c B Mq Bq : ℝ, 0 ≤ c → Mq * c ^ B < Bq → Bq ≤ 999 / 1000 →
      M ≤ ENNReal.ofReal Mq → ENNReal.ofReal (c ^ B) * M ≤ ENNReal.ofReal (999 / 1000) := by
    intro c B Mq Bq hc hgate hBq hMq
    calc ENNReal.ofReal (c ^ B) * M ≤ ENNReal.ofReal (c ^ B) * ENNReal.ofReal Mq :=
          mul_le_mul_right hMq _
      _ = ENNReal.ofReal (Mq * c ^ B) := by
          rw [← ENNReal.ofReal_mul (rpow_nonneg hc B), mul_comm]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hgate.le.trans hBq)
  have hmax : ∀ r U : ℕ, ((m : ℤ) - ((r + U : ℕ) : ℤ) : ℝ) ≤
      ((max ((m : ℤ) - ((r + U : ℕ) : ℤ)) 1 : ℤ) : ℝ) := fun r U ↦ by
    exact_mod_cast le_max_left _ _
  obtain ⟨B, c₀, hAB, hB3, hG, hmass⟩ : ∃ B c₀ : ℝ, A ≤ B ∧ B ≤ 3 ∧
      (∀ r U : ℕ, (r : ℝ) ≤ ω / 4 + u → (U : ℝ) ≤ u →
        (m : ℝ) ≤ c₀ * ((max ((m : ℤ) - ((r + U : ℕ) : ℤ)) 1 : ℤ) : ℝ)) ∧
      ENNReal.ofReal (c₀ ^ B) * M ≤ ENNReal.ofReal (999 / 1000) := by
    cases ι with
    | o =>
      have hA' : A ≤ 11 / 5 := by rw [Aexp_cast_o] at hA; linarith
      have hω32 : (ω : ℝ) ≤ 3 / 2 * m := by rw [gapSplit_o] at hωR; linarith
      rcases le_or_gt (2 ^ 34) ω with h34 | h34
      · refine ⟨11 / 5, 2048 / 1279, hA', by norm_num, fun r U hr hU ↦ ?_,
          hfin _ _ _ (999 / 1000) (by norm_num) ?_ le_rfl (hML h34)⟩
        · have := hmax r U
          push_cast at this ⊢
          rw [hu] at hr hU
          linarith
        · exact c3NeartopPaid_gate (k := 5) (j := 11) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num)
      · refine ⟨11 / 5, 2048 / 2045, hA', by norm_num, fun r U hr hU ↦ ?_,
          hfin _ _ _ (97 / 100) (by norm_num) ?_ (by norm_num) (hMS h34)⟩
        · have := hmax r U
          push_cast at this ⊢
          have h34' : (ω : ℝ) < 2 ^ 34 := by exact_mod_cast h34
          rw [hu] at hr hU
          linarith
        · exact c3NeartopPaid_gate (k := 5) (j := 11) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num)
    | b =>
      have hA' : A ≤ 17 / 10 := by rw [Aexp_cast_b] at hA; linarith
      rcases le_or_gt (2 ^ 34) ω with h34 | h34
      · refine ⟨17 / 10, 2048 / 1023, hA', by norm_num, fun r U hr hU ↦ ?_,
          hfin _ _ _ (999 / 1000) (by norm_num) ?_ le_rfl (hML h34)⟩
        · have := hmax r U
          push_cast at this ⊢
          rw [hu] at hr hU
          linarith
        · exact c3NeartopPaid_gate (k := 10) (j := 17) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num)
      · refine ⟨17 / 10, 2048 / 2045, hA', by norm_num, fun r U hr hU ↦ ?_,
          hfin _ _ _ (97 / 100) (by norm_num) ?_ (by norm_num) (hMS h34)⟩
        · have := hmax r U
          push_cast at this ⊢
          have h34' : (ω : ℝ) < 2 ^ 34 := by exact_mod_cast h34
          rw [hu] at hr hU
          linarith
        · exact c3NeartopPaid_gate (k := 10) (j := 17) (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num)
  set f₁ : trAtoms n → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e ω a) *
    (if (ω : ℝ) / 4 + u < (a.1.1.1 : ℝ) then 1 else 0) with hf₁
  set f₂ : trAtoms n → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e ω a) *
    (if u < ((((a.1.2.take 1).map fun b ↦ bkJ (chBlockPoint b)).sum : ℤ) : ℝ) then 1 else 0)
    with hf₂
  set E := exp (-((m : ℝ) / 2 ^ 26)) with hE
  have hT₁ : ∑' a, f₁ a ≤ ENNReal.ofReal (6 * E) := by
    have hfac : ∀ a : trAtoms n, f₁ a = (fun rl : ℕ × ℤ ↦
        ENNReal.ofReal (firstPassageLaw ω ((rl.1 : ℤ), rl.2)) *
          (if (ω : ℝ) / 4 + u < (rl.1 : ℝ) then 1 else 0)) a.1.1 *
        ENNReal.ofReal (trListWeight a.1.2) := fun a ↦ by
      simp only [hf₁, trFreshLaw_def, ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _)]
      ring
    exact (tsum_congr hfac).trans_le ((tsum_trAtoms_mul_trListWeight _).trans_le
      (c3NeartopPaid_hor_tail hm hωm))
  have hT₂ : ∑' a, f₂ a ≤ ENNReal.ofReal E :=
    (c3NeartopPaid_tsum_trFreshLaw_hold n e ω hJ hu2).trans
      (ENNReal.ofReal_le_ofReal (exp_le_exp.2 (by rw [hu]; nlinarith)))
  have hsmall := c3NeartopPaid_small hmr
  rw [← hE] at hsmall
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hm3E : 0 ≤ (m : ℝ) ^ 3 * E := mul_nonneg (pow_nonneg hm0 3) hE0
  have hmain : ENNReal.ofReal (chQ n ξ (epsStar : ℝ) e) ≤
      ENNReal.ofReal K * ENNReal.ofReal (1999 / 2000) := by
    refine (chQ_le_tsum_trFreshLaw_mul_exp n ξ he hb le_rfl hJ).trans ?_
    refine (ENNReal.tsum_le_tsum fun a ↦
      c3NeartopPaid_atom he hA₀ hAB hB3 hm1 hjm hωZ hG a).trans ?_
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      ENNReal.tsum_add]
    refine mul_le_mul_right ?_ _
    calc ENNReal.ofReal (c₀ ^ B) * M +
          ENNReal.ofReal ((m : ℝ) ^ 3) * (∑' a, f₁ a + ∑' a, f₂ a)
        ≤ ENNReal.ofReal (999 / 1000) +
          ENNReal.ofReal ((m : ℝ) ^ 3) * (ENNReal.ofReal (6 * E) + ENNReal.ofReal E) :=
          add_le_add hmass (mul_le_mul_right (add_le_add hT₁ hT₂) _)
      _ = ENNReal.ofReal (999 / 1000 + (m : ℝ) ^ 3 * (6 * E + E)) := by
          rw [← ENNReal.ofReal_add (by positivity) hE0, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by norm_num) (by positivity)]
      _ ≤ ENNReal.ofReal (1999 / 2000) := ENNReal.ofReal_le_ofReal (by
          have h7 : (m : ℝ) ^ 3 * (6 * E + E) ≤ 8 * (m : ℝ) ^ 3 * E := by nlinarith
          have h20 : (1 : ℝ) / 2 ^ 20 ≤ 1 / 2000 := by norm_num
          linarith)
  rw [← ENNReal.ofReal_mul hK0, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain
  rw [hK] at hmain
  linarith

end CollatzPosDens
