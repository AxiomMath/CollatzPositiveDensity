/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.CharSum.ChQStopped
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.CharSum.ChBoundaryStep
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.D1
public import CollatzPosDens.Transfer.Dexp
public import CollatzPosDens.Transfer.Dpt
public import CollatzPosDens.Monotone.MoRate
public import CollatzPosDens.Monotone.MoRateD1
public import CollatzPosDens.Monotone.MoCase2Margin
public import CollatzPosDens.Monotone.MoConeEndpoint
public import CollatzPosDens.Monotone.MoEnvelope
public import CollatzPosDens.Monotone.MoMomentThreshold
public import CollatzPosDens.Monotone.MoWhiteGain
public import CollatzPosDens.Monotone.MoDiscountedExpectation
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpFinite
public import CollatzPosDens.Renewal.RnFpMgf
public import CollatzPosDens.Renewal.RnFpMgfSummable
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.Renewal.RnP45Floor
public import CollatzPosDens.Renewal.RnP45Mass

/-!
# The near-top case of the monotonicity step

Let `ξ ∈ G_n` be a unit and let `m` be an integer with `m ≥ D_pt` and `m ≥ D_exp`. Let `p ∈ 𝒫`
with `j(p) + m = J = ⌊n/2⌋`, and let `Δ ∈ 𝔗_{n,ξ,ε_*}` with `p ∈ Δ` and
`l_Δ - l(p) ≤ m / (log m)²`. Then `Q(p) ≤ m^{-A_*} Q_{m-1}`.

With `s = l_Δ - l(p)`, `t = rt_{A_*}(m)` and `C = m^{-A_*} Q_{m-1}`, the stopped inequality
bounds `Q(p)` by the `F_s`-average of `Q(p + x)`. Every branch satisfies `Q(p + x) ≤ C e^{t r}`
(`chQ_le_boundary_step` and `max_sub_one_rpow_neg_le_mul_exp_moRate`), and a branch in the cone
`V = {(r, ℓ) : 1 ≤ r ≤ ⌊(5s + 16)/16⌋, s + 1 ≤ ℓ ≤ s + 4}` the discounted bound
`Q(p + x) ≤ C e^{-(z_* - w_*/2)} e^{t r}` (`chQ_coneEndpoint_le`). The discounted expectation,
the moment bound `∑ F_s(x) e^{t r} ≤ 1 + w_*/8`, the cone mass `p₄₅(s) ≥ 3/16` and the white
gain `e^{-z_* + w_*/2} ≤ 1 - (3/5) z_*` combine to `C (1 + w_*/8 - (3/5) z_* · 3/16) ≤ C`.

## Main results

* `CollatzPosDens.chQ_le_rpow_mul_chQm_of_mem_bkFamily`: the near-top bound.

## Implementation notes

The integer `m` is taken in `ℕ`: the hypothesis `m ≥ D_pt > 0` forces `m ≥ 1`. The hypothesis
`p ∈ 𝒫` is implied by `p ∈ Δ` and is omitted.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- Over `ℕ × ℤ`, the tilted law `F_s(x) e^{t r}` is summable, with total mass at most `c`
whenever `11 e^t < 16` and `M₄₅(t)^{s+1} ≤ c`. -/
private theorem moCase2_summable_and_tsum_le {s : ℕ} {t c : ℝ} (ht0 : 0 ≤ t)
    (ht16 : 11 * exp t < 16) (hc : 0 ≤ c) (h : mgfNu45 t ^ (s + 1) ≤ ENNReal.ofReal c) :
    (Summable fun x : ℕ × ℤ ↦ firstPassageLaw s ((x.1 : ℤ), x.2) * exp (t * x.1)) ∧
      ∑' x : ℕ × ℤ, firstPassageLaw s ((x.1 : ℤ), x.2) * exp (t * x.1) ≤ c := by
  set ι : ℕ × ℤ → ℤ × ℤ := fun x ↦ ((x.1 : ℤ), x.2) with hι
  have hinj : Function.Injective ι := natCast_prod_injective
  set f : ℤ × ℤ → ℝ := fun x ↦ firstPassageLaw s x * exp (t * x.1) with hfdef
  have hf0 : ∀ x, 0 ≤ f x := fun x ↦ mul_nonneg (firstPassageLaw_nonneg _ _) (exp_pos _).le
  have hfs : Summable f := summable_firstPassageLaw_mul_exp s ht0 ht16
  have hcomp : (fun x : ℕ × ℤ ↦ firstPassageLaw s ((x.1 : ℤ), x.2) * exp (t * x.1)) =
      f ∘ ι := by
    funext x
    simp [hfdef, hι]
  have h1 := tsum_ofReal_firstPassageLaw_mul_exp_le s ht0
  rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs] at h1
  rw [hcomp]
  exact ⟨hfs.comp_injective hinj, (tsum_comp_le_tsum_of_inj hfs hf0 hinj).trans
    ((ENNReal.ofReal_le_ofReal_iff hc).1 (h1.trans h))⟩

/-- The cone `V = [1, ⌊(5s + 16)/16⌋] × [s + 1, s + 4]` carries `F_s`-mass `p₄₅(s)`. -/
private theorem moCase2_tsum_cone (s : ℕ) :
    ∑' x : {x : ℕ × ℤ | 1 ≤ x.1 ∧ x.1 ≤ (5 * s + 16) / 16 ∧ (s : ℤ) + 1 ≤ x.2 ∧
        x.2 ≤ (s : ℤ) + 4},
      firstPassageLaw s ((x.1.1 : ℤ), x.1.2) = p45 s := by
  have hV : {x : ℕ × ℤ | 1 ≤ x.1 ∧ x.1 ≤ (5 * s + 16) / 16 ∧ (s : ℤ) + 1 ≤ x.2 ∧
      x.2 ≤ (s : ℤ) + 4} =
      ↑(Finset.Icc 1 ((5 * s + 16) / 16) ×ˢ Finset.Icc ((s : ℤ) + 1) ((s : ℤ) + 4)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc,
      and_assoc]
  rw [hV]
  refine (Finset.tsum_subtype _ fun x : ℕ × ℤ ↦ firstPassageLaw s ((x.1 : ℤ), x.2)).trans ?_
  rw [Finset.sum_product, ← sum_firstPassageLaw_eq_p45 s]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have : Finset.Icc ((s : ℤ) + 1) ((s : ℤ) + 4) =
      (Finset.Icc (1 : ℤ) 4).map (addLeftEmbedding (s : ℤ)) := by
    rw [Finset.map_add_left_Icc]
  rw [this, Finset.sum_map]
  rfl

/-- The envelope bound `max(m - r, 1)^{-A} Q ≤ m^{-A} Q e^{rt_A(m) r}` for `Q ≥ 0`. -/
theorem max_sub_rpow_neg_mul_le_mul_exp_moRate {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 1 ≤ m)
    {Q : ℝ} (hQ : 0 ≤ Q) (r : ℕ) :
    max ((m : ℝ) - r) 1 ^ (-A) * Q ≤ (m : ℝ) ^ (-A) * Q * exp (moRate A m * r) := by
  have hcast : max ((m : ℝ) - r) 1 = ((max (m - r) 1 : ℕ) : ℝ) := by
    rcases le_total r m with h | h
    · rw [Nat.cast_max, Nat.cast_sub h]
      simp
    · rw [Nat.sub_eq_zero_of_le h]
      simp [max_eq_right (by linarith [(by exact_mod_cast h : (m : ℝ) ≤ r)] : (m : ℝ) - r ≤ 1)]
  rw [hcast, mul_right_comm]
  exact mul_le_mul_of_nonneg_right (max_sub_one_rpow_neg_le_mul_exp_moRate hA hm r) hQ

/-- For `0 ≤ t ≤ 1/1024`, `11 e^t < 16`. -/
theorem eleven_mul_exp_lt_sixteen {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 1024) :
    11 * exp t < 16 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := t) (by rw [abs_le]; constructor <;> linarith)
  rw [abs_le] at h
  nlinarith [h.2]

/-- A branch `x = (r, ℓ)` in the support of `F_s`, taken from `p ∈ 𝒫` with `j(p) + m = ⌊n/2⌋`,
satisfies `Q(p + x) ≤ max(m - r, 1)^{-A} Q_{m-1}`. -/
theorem chQ_add_le_of_firstPassageLaw_ne_zero {n : ℕ} (ξ : ResidueGroup n) (ε : ℝ) {A : ℝ}
    (hA : 0 ≤ A) {m : ℕ} {p : ℤ × ℤ} (hp : p ∈ bkPoints) (hpm : bkJ p + m = ((n / 2 : ℕ) : ℤ))
    {s : ℤ} {r : ℕ} {ℓ : ℤ} (hF : firstPassageLaw s ((r : ℤ), ℓ) ≠ 0) :
    chQ n ξ ε (p + ((r : ℤ), ℓ)) ≤ max ((m : ℝ) - r) 1 ^ (-A) * chQm n ξ ε A (m - 1) := by
  have hr : 1 ≤ r := by
    have := (firstPassageLaw_support hF).1
    dsimp only at this
    omega
  have hpx : p + ((r : ℤ), ℓ) ∈ bkPoints := by
    rw [add_mem_bkPoints_iff]
    rw [mem_bkPoints] at hp
    simp only [bkJ] at hp ⊢
    omega
  have hj : bkJ (p + ((r : ℤ), ℓ)) + m = ((n / 2 : ℕ) : ℤ) + r := by
    simp only [bkJ, Prod.fst_add] at hpm ⊢
    omega
  have hcast : ((max ((m : ℤ) - r) 1 : ℤ) : ℝ) = max ((m : ℝ) - r) 1 := by
    push_cast
    rfl
  simpa only [hcast] using chQ_le_boundary_step n ξ ε hA hr hpx hj

/-- For `m ≥ D₁`, the rate `t = rt_{A_*}(m)` satisfies `11 e^t < 16`. -/
theorem eleven_mul_exp_moRate_lt_sixteen {m : ℕ} (hm : (D1 : ℝ) ≤ m) :
    11 * exp (moRate (Aexp : ℝ) m) < 16 := by
  have hA : (0 : ℝ) ≤ (Aexp : ℝ) := by rw [Aexp_cast]; norm_num
  have ht32 : moRate (Aexp : ℝ) m ≤ (wStar : ℝ) / 32 := by
    refine moRate_le_div_thirtyTwo hA (by rw [wStar_cast]; norm_num) ?_
    rw [D1_def] at hm
    exact_mod_cast hm
  exact eleven_mul_exp_lt_sixteen (moRate_nonneg hA m) (ht32.trans (by rw [wStar_cast]; norm_num))

/-- A branch `x = (r, ℓ)` in the cone `V`, taken from `p ∈ Δ` at level `s = l_Δ - l(p)`, satisfies
`Q(p + x) ≤ m^{-A_*} Q_{m-1} e^{-(z_* - w_*/2)} e^{rt_{A_*}(m) r}`. -/
theorem chQ_add_le_mul_exp_of_mem_cone {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {m : ℕ} (hmpt : (Dpt : ℝ) ≤ m) {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (hpm : bkJ p + m = ((n / 2 : ℕ) : ℤ)) {Δ : BkTriangle}
    (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ)) (hpΔ : p ∈ Δ) {s : ℕ} (hs : bkL p + s = Δ.l)
    (hsm : (s : ℝ) ≤ m / Real.log m ^ 2) {r : ℕ} {ℓ : ℤ} (hr₁ : 1 ≤ r)
    (hr : r ≤ (5 * s + 16) / 16) (hℓ₁ : (s : ℤ) + 1 ≤ ℓ) (hℓ₄ : ℓ ≤ (s : ℤ) + 4) :
    chQ n ξ (epsStar : ℝ) (p + ((r : ℤ), ℓ)) ≤
      (m : ℝ) ^ (-(Aexp : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) *
        exp (-((zStar : ℝ) - (wStar : ℝ) / 2)) * exp (moRate (Aexp : ℝ) m * r) := by
  have hm1 : 1 ≤ m := by
    exact_mod_cast (le_trans (by rw [Dpt_cast]; norm_num) hmpt : (1 : ℝ) ≤ m)
  have hcone := chQ_coneEndpoint_le hξ hmpt hp hpm hΔ hpΔ hs hsm hr₁ hr
    (O := ℓ - s) (by omega) (by omega)
  rw [show (s : ℤ) + (ℓ - s) = ℓ by ring] at hcone
  refine hcone.trans ?_
  rw [show -((zStar : ℝ) - (wStar : ℝ) / 2) = -(zStar : ℝ) + (wStar : ℝ) / 2 by ring]
  calc _ = exp (-(zStar : ℝ) + (wStar : ℝ) / 2) * (max ((m : ℝ) - r) 1 ^ (-(Aexp : ℝ)) *
        chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_sub_rpow_neg_mul_le_mul_exp_moRate
        (by rw [Aexp_cast]; norm_num) hm1 (chQm_nonneg _ _ _ _ _) r) (exp_pos _).le
    _ = _ := by ring

/-- **The near-top case.** Let `ξ ∈ G_n` be a unit, `m ≥ D_pt`, `m ≥ D_exp`, `p` with
`j(p) + m = ⌊n/2⌋`, and `Δ ∈ 𝔗_{n,ξ,ε_*}` with `p ∈ Δ` and `l_Δ - l(p) ≤ m / (log m)²`. Then
`Q(p) ≤ m^{-A_*} Q_{m-1}`. -/
@[collatz_pos_dens "lem_mo_case2"]
theorem chQ_le_rpow_mul_chQm_of_mem_bkFamily {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {m : ℕ} (hmpt : (Dpt : ℝ) ≤ m) (hmexp : Dexp ≤ m)
    {p : ℤ × ℤ} (hpm : bkJ p + m = ((n / 2 : ℕ) : ℤ))
    {Δ : BkTriangle} (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ)) (hpΔ : p ∈ Δ)
    (hlm : ((Δ.l - bkL p : ℤ) : ℝ) ≤ m / Real.log m ^ 2) :
    chQ n ξ (epsStar : ℝ) p ≤
      (m : ℝ) ^ (-(Aexp : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) := by
  have hp : p ∈ bkPoints := BkTriangle.mem_bkPoints_of_mem hpΔ
  have hA : (0 : ℝ) ≤ (Aexp : ℝ) := by rw [Aexp_cast]; norm_num
  have hm₁ : (D1 : ℝ) ≤ m := le_trans (by exact_mod_cast D1_lt_Dpt.le) hmpt
  have hm1 : 1 ≤ m := by
    exact_mod_cast (le_trans (by rw [Dpt_cast]; norm_num) hmpt : (1 : ℝ) ≤ m)
  set s : ℕ := (Δ.l - bkL p).toNat
  have hsZ : ((s : ℕ) : ℤ) = Δ.l - bkL p :=
    Int.toNat_of_nonneg (sub_nonneg.2 (BkTriangle.le_l_of_mem hpΔ))
  have hs : bkL p + s = Δ.l := by omega
  have hsm : (s : ℝ) ≤ m / Real.log m ^ 2 := by
    rwa [← hsZ, Int.cast_natCast] at hlm
  set t : ℝ := moRate (Aexp : ℝ) m
  have ht0 : 0 ≤ t := moRate_nonneg hA m
  set C : ℝ := (m : ℝ) ^ (-(Aexp : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1)
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (chQm_nonneg _ _ _ _ _)
  obtain ⟨hsumN, hmomN⟩ := moCase2_summable_and_tsum_le ht0
    (eleven_mul_exp_moRate_lt_sixteen hm₁) (by rw [wStar_cast]; norm_num)
    (mgfNu45_moRate_pow_le hm₁ hmexp hsm)
  have hbranch : ∀ x : ℕ × ℤ, firstPassageLaw s ((x.1 : ℤ), x.2) ≠ 0 →
      chQ n ξ (epsStar : ℝ) (p + ((x.1 : ℤ), x.2)) ≤ C * exp (t * x.1) := fun ⟨r, _⟩ hF ↦
    (chQ_add_le_of_firstPassageLaw_ne_zero ξ _ hA hp hpm hF).trans
      (max_sub_rpow_neg_mul_le_mul_exp_moRate hA hm1 (chQm_nonneg _ _ _ _ _) r)
  set V : Set (ℕ × ℤ) := {x : ℕ × ℤ | 1 ≤ x.1 ∧ x.1 ≤ (5 * s + 16) / 16 ∧
    (s : ℤ) + 1 ≤ x.2 ∧ x.2 ≤ (s : ℤ) + 4} with hVdef
  have hloc : ∀ x ∈ V, firstPassageLaw s ((x.1 : ℤ), x.2) ≠ 0 →
      chQ n ξ (epsStar : ℝ) (p + ((x.1 : ℤ), x.2)) ≤
        C * exp (-((zStar : ℝ) - (wStar : ℝ) / 2)) * exp (t * x.1) := by
    rintro ⟨r, ℓ⟩ ⟨hr₁, hr, hℓ₁, hℓ₄⟩ -
    exact chQ_add_le_mul_exp_of_mem_cone hξ hmpt hp hpm hΔ hpΔ hs hsm hr₁ hr hℓ₁ hℓ₄
  have hd : exp (-((zStar : ℝ) - (wStar : ℝ) / 2)) ≤ 1 - 3 / 5 * (zStar : ℝ) := by
    rw [show -((zStar : ℝ) - (wStar : ℝ) / 2) = -(zStar : ℝ) + (wStar : ℝ) / 2 by ring]
    exact exp_neg_zStar_add_wStar_div_two_le
  have hc : (0 : ℝ) ≤ 3 / 5 * (zStar : ℝ) := by rw [zStar_cast]; norm_num
  have hexp := tsum_mul_le_of_le_exp_discount (V := V)
    (μ := fun x : ℕ × ℤ ↦ firstPassageLaw s ((x.1 : ℤ), x.2))
    (F := fun x : ℕ × ℤ ↦ chQ n ξ (epsStar : ℝ) (p + ((x.1 : ℤ), x.2)))
    (g := fun x : ℕ × ℤ ↦ t * x.1) (C := C)
    (fun x ↦ firstPassageLaw_nonneg _ _) (fun x ↦ (chQ_range n ξ _ _).1)
    (fun x ↦ mul_nonneg ht0 (Nat.cast_nonneg _)) hC hc hd hsumN hbranch hloc
  have hmass : (3 / 16 : ℝ) ≤ ∑' x : V, firstPassageLaw s ((x.1.1 : ℤ), x.1.2) := by
    rw [hVdef, moCase2_tsum_cone s]
    exact three_div_sixteen_le_p45 s
  refine (chQ_le_tsum_firstPassageLaw_mul n ξ _ s hp).trans
    (hexp.trans ((mul_le_mul_of_nonneg_left ?_ hC).trans_eq (mul_one C)))
  linarith [mul_le_mul_of_nonneg_left hmass hc, moCase2_margin_cast (K := ℝ)]

end CollatzPosDens
