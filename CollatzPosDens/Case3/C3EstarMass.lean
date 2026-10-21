/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkCover
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.Case3.C3EprimeMass
public import CollatzPosDens.Case3.C3FreshDevMass
public import CollatzPosDens.Case3.C3GapTop
public import CollatzPosDens.Case3.C3GoodMarginal
public import CollatzPosDens.Case3.C3InitExceptionMass
public import CollatzPosDens.Case3.C3InitialMass
public import CollatzPosDens.Case3.C3Margin
public import CollatzPosDens.Case3.C3Near
public import CollatzPosDens.Case3.C3OutsideMass
public import CollatzPosDens.Case3.C3PaidDom
public import CollatzPosDens.Case3.C3PaidLaw
public import CollatzPosDens.Case3.C3StageDiscount
public import CollatzPosDens.Case3.C3StageTimesB
public import CollatzPosDens.Case3.C3TimedStages
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrClearMass
public import CollatzPosDens.StoppingTrace.TrDiscountedTrace
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrPrefixFreeMass
public import CollatzPosDens.StoppingTrace.TrSurvivalTime
public import CollatzPosDens.Transfer.S02AiPos
public import CollatzPosDens.Transfer.S02EpsInit
public import CollatzPosDens.Transfer.S02Eta
public import CollatzPosDens.Transfer.S02FarS
public import CollatzPosDens.Transfer.S02Gamma
public import CollatzPosDens.Transfer.S02OmegaLower
public import CollatzPosDens.Transfer.S02PBits
public import CollatzPosDens.Transfer.S02PiAd
public import CollatzPosDens.Transfer.S02RhoPk
public import CollatzPosDens.Transfer.S02ScheduleValues
public import CollatzPosDens.Transfer.S02Split
public import CollatzPosDens.Transfer.S02Ud
public import CollatzPosDens.Transfer.S02Uo
public import CollatzPosDens.Transfer.S02Uv
public import CollatzPosDens.Transfer.S02WeightedSqrt
public import CollatzPosDens.Transfer.S02WidthGate
public import CollatzPosDens.Transfer.S02Z

/-!
# Discounted paid mass of the low, unadvanced atoms

Let `ι ∈ 𝔍` be a Fourier index, `J = ⌊n/2⌋`, let `ξ ∈ G_n` be a unit, `Δ ∈ 𝔗 = 𝔗_{n,ξ,ε_*}`,
`e ∈ Δ` with gap `ω = gap(e)`, and let `m ≥ D_sc(ι)` be an integer with `j(e) + m = J`,
`P_*(ι) ≤ J` and `ς(ι, m) < ω`, where `ς` is the split level of the gap.
Then the paid fresh law `μ̃_e`, discounted by `exp(-z_* N^e_{P_*(ι)-1})`, puts mass at most
$$\Pi_{ad} + q_{mass} \eta_{r_*} + \mathcal E_{sq} + U_o + \epsilon_{init}
  + q_{mass}(U_v + U_d + E_{piece})$$
on the atoms of `Low^e(ι) \ Bad^e_m(ι)`, where every recipe constant is taken at `ι` and
`η_i = η_i(ι)` are the event coefficients.

The proof splits the paid passage mass `F̃_e = F^gd_e + F^ex_e`, where `F^ex_e` is carried by the
common initial exception `𝓑_init(ω)`; as discounts are at most `1` and block lists of length `J`
have total weight `1`, the part carried by `F^ex_e` is at most `bw^⊗(𝓑_init(ω)) ≤ ε_init`. The
filtered marginal `F^gd_e` has total mass below `q_mass` and is dominated by `F_ω`. Its atoms
with `(r, ℓ)` in the initial deviation set `𝓘_ω` carry at most `U_o + (2ω)^{-1/2}`; those in the
fresh deviation event `Dev^fr` or the slow clearing event `Clr`, both depending on the block list
only, carry at most `q_mass (U_v + U_d + E_piece)`. Every remaining atom of positive mass either
has no oversize hit up to time `p_{r_*-1}`, or has a first oversize hit in a window
`(p_{i-1}, p_i]`, `i < r_*`. An atom of the class `k` (the first class being `k = r_*`) is
discounted by the factor `η_k`: for `ι = o`, and for `ι = b` with `k ≤ 1`,
`le_trNu_and_trStopTime_le_schedule` gives the stopping time `τ_{k+1} ≤ P_* - 1` and
`tsum_ofReal_mul_exp_neg_trWhiteCount_le` gives `θ^en_k = η_k`; for `ι = b` with `k ∈ {2, 3}`,
the timed stages (gap threshold `4096`, stage length `5`, deadlines `(169, 503672, 63696221)`)
complete `k - 1` stages by time `p_k`, and `tsum_ofReal_mul_exp_neg_trWhiteCount_le_stageRate`
gives `max(b_*, (77/100)^5)^{k-1} = b_*^{k-1} = η_k`. An atom of the `i`-th class lies in
`Big_{e,p_i,S_i}` and outside `Dev_{ω,p_i}`, so its first column lies in the anchor columns `𝒰_i`,
whose filtered mass is bounded by `BkBlack.tsum_tsum_c3GoodMarginal_c3AnchorCols_le`. Summing over
`i < r_*`, using `√ω ≥ R_Ω`, produces `Π_ad` and the square-root allowance `𝓔_sq`.

## Main results

* `CollatzPosDens.tsum_trFreshLaw_trEStar_lt`: the bound on the discounted paid mass of
  `Low^e(ι) \ Bad^e_m(ι)`.

## Implementation notes

The paid fresh law is `ℝ≥0∞`-valued, so the mass is the `ℝ≥0∞`-valued sum
`∑' a : Low^e \ Bad^e_m, μ̃_e(a) exp(-z_* N^e_{P_*-1}(a))`, which needs no summability side
condition, and the bound is stated for its image under `ENNReal.ofReal`. The integer `m` is
taken in `ℕ`, as the event `Bad^e_m` is indexed by `ℕ`; this loses nothing since `m ≥ D_sc > 0`.
The gap `ω = gap(e)` is a nonnegative integer, used as a natural number.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

open Finset

variable {ι : FIndex} {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ}

/-- The paid fresh law is dominated by the fresh law at the gap: if `gap(e) ≥ 0`, then
`μ̃_e(a) ≤ μ_{e,gap(e)}(a)` for every atom `a`. -/
theorem c3PaidLaw_le_ofReal_trFreshLaw (hω : 0 ≤ trGap n ξ (epsStar : ℝ) e)
    (a : (ℕ × ℤ) × List (List ℤ × ℤ)) :
    c3PaidLaw n ξ e a ≤
      ENNReal.ofReal (trFreshLaw n e (trGap n ξ (epsStar : ℝ) e).toNat a) := by
  obtain ⟨⟨r, ℓ⟩, β⟩ := a
  rw [c3PaidLaw_mk, trFreshLaw_mk, ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _),
    Int.toNat_of_nonneg hω]
  gcongr
  exact (c3PaidPassage_le_firstPassageLaw n ξ e _).2

/-- The paid passage mass is finite. -/
theorem c3PaidPassage_ne_top (x : ℤ × ℤ) : c3PaidPassage n ξ e x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (c3PaidPassage_le_firstPassageLaw n ξ e x).2

/-- The filtered paid marginal is finite. -/
theorem c3GoodMarginal_ne_top (ι : FIndex) (x : ℤ × ℤ) : c3GoodMarginal ι n ξ e x ≠ ⊤ :=
  ne_top_of_le_ne_top (c3PaidPassage_ne_top x) (c3GoodMarginal_le_c3PaidPassage ι n ξ e x)

/-- The filtered paid marginal is dominated by the first-passage law at the gap. -/
theorem c3GoodMarginal_le_ofReal_firstPassageLaw (ι : FIndex) (x : ℤ × ℤ) :
    c3GoodMarginal ι n ξ e x ≤ ENNReal.ofReal (firstPassageLaw (trGap n ξ (epsStar : ℝ) e) x) :=
  (c3GoodMarginal_le_c3PaidPassage ι n ξ e x).trans (c3PaidPassage_le_firstPassageLaw n ξ e x).2

/-- A sum over the fresh atoms `𝒜_n = (ℕ × ℤ) × 𝔅^J` of a product splits as a product of sums. -/
theorem tsum_trAtoms_mul (h : ℕ × ℤ → ℝ≥0∞) (k : List (List ℤ × ℤ) → ℝ≥0∞) :
    ∑' a : trAtoms n, h a.1.1 * k a.1.2 =
      (∑' x, h x) * ∑' β : {β : List (List ℤ × ℤ) //
        β.length = n / 2 ∧ ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}}, k β.1 := by
  rw [← (trAtomsEquiv n).symm.tsum_eq]
  change ∑' c : (ℕ × ℤ) × {β : List (List ℤ × ℤ) //
    β.length = n / 2 ∧ ∀ x ∈ β, x ∈ {x : List ℤ × ℤ | x.2 ∈ ({4, 5} : Set ℤ)}},
      h c.1 * k c.2.1 = _
  refine (ENNReal.tsum_prod (f := fun x β ↦ h x * k (Subtype.val β))).trans ?_
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr fun x ↦ ENNReal.tsum_mul_left

/-- Block lists of length `J` have total weight `1`, so a product with the block weight sums over
the fresh atoms to the sum over displacements. -/
theorem tsum_trAtoms_mul_trListWeight (h : ℕ × ℤ → ℝ≥0∞) :
    ∑' a : trAtoms n, h a.1.1 * ENNReal.ofReal (trListWeight a.1.2) = ∑' x, h x := by
  rw [tsum_trAtoms_mul h (fun β ↦ ENNReal.ofReal (trListWeight β)),
    tsum_ofReal_trListWeight_length_eq, mul_one]

/-- The first-passage law restricted to `ℕ × ℤ` has total mass `1`, as a sum in `[0, ∞]`. -/
theorem tsum_ofReal_firstPassageLaw_natCast (s : ℕ) :
    ∑' x : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw s ((x.1 : ℤ), x.2)) = 1 := by
  rw [natCast_prod_injective.tsum_eq (f := fun x ↦ ENNReal.ofReal (firstPassageLaw s x)),
    ← ENNReal.ofReal_tsum_of_nonneg (firstPassageLaw_nonneg s) (summable_firstPassageLaw s),
    tsum_firstPassageLaw, ENNReal.ofReal_one]
  intro x hx
  rw [Function.mem_support] at hx
  have h2 : firstPassageLaw s x ≠ 0 := fun h0 ↦ hx (by rw [h0, ENNReal.ofReal_zero])
  have h1 := (firstPassageLaw_support h2).1
  exact ⟨(x.1.toNat, x.2), Prod.ext (Int.toNat_of_nonneg (by omega)) rfl⟩

/-- **Discounted trace mass for the filtered marginal.** Let `ξ` be a unit, `e ∈ 𝒫`, `k ∈ ℕ`,
`D ⊆ ℕ × ℤ` and `S ⊆ 𝒜_n` a set of atoms `a = ((r, ℓ), β)` with `(r, ℓ) ∈ D` whose fresh path
has its stopping time `τ_{k+1}` defined and at most `P_* - 1`. Then
`∑_{a ∈ S} F^gd_e(r, ℓ) bw^⊗(β) exp(-z_* N^e_{P_*-1}(a)) ≤ θ^en_k ∑_{(r, ℓ) ∈ D} F^gd_e(r, ℓ)`. -/
theorem tsum_c3GoodMarginal_mul_exp_neg_trWhiteCount_le (ι : FIndex) (hξ : IsResidueUnit ξ)
    (he : e ∈ bkPoints) (k : ℕ) (D : Set (ℕ × ℤ)) (S : Set ((ℕ × ℤ) × List (List ℤ × ℤ)))
    (hS : S ⊆ trAtoms n) (hSD : ∀ a ∈ S, a.1 ∈ D)
    (hSτ : ∀ a ∈ S, ∃ t, trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) (k + 1) = some t ∧
      t ≤ pStar ι - 1) :
    ∑' a : S, c3GoodMarginal ι n ξ e ((a.1.1.1 : ℤ), a.1.1.2) *
        ENNReal.ofReal (trListWeight a.1.2) *
        ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1)))) ≤
      ENNReal.ofReal (thetaEn k : ℝ) * ∑' x : D, c3GoodMarginal ι n ξ e ((x.1.1 : ℤ), x.1.2) := by
  have h := tsum_ofReal_mul_exp_neg_trWhiteCount_le ι hξ he k
    (fun x ↦ (c3GoodMarginal ι n ξ e ((x.1 : ℤ), x.2)).toReal) D S hS hSD hSτ
  have hz : (gammaStar : ℝ) = zStar := by rw [gammaStar_cast, zStar_cast]
  have hL : ∀ a : S, c3GoodMarginal ι n ξ e ((a.1.1.1 : ℤ), a.1.1.2) *
      ENNReal.ofReal (trListWeight a.1.2) *
      ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1)))) =
      ENNReal.ofReal ((c3GoodMarginal ι n ξ e ((a.1.1.1 : ℤ), a.1.1.2)).toReal *
        trListWeight a.1.2 *
        Real.exp (-((gammaStar : ℝ) * trWhiteCount n ξ e a.1 (pStar ι - 1)))) := by
    intro a
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (trListWeight_nonneg _)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (c3GoodMarginal_ne_top ι _),
      hz]
  refine (le_of_eq (tsum_congr hL)).trans (h.trans_eq ?_)
  congr 1
  exact tsum_congr fun x ↦ ENNReal.ofReal_toReal (c3GoodMarginal_ne_top ι _)

/-- **Stage-discounted mass for the filtered marginal.** Let `ξ` be a unit, `e ∈ 𝒫`, `d ≥ 1`,
`k ∈ ℕ`, `D ⊆ ℕ × ℤ` and `S ⊆ 𝒜_n` a set of atoms `a = ((r, ℓ), β)` with `(r, ℓ) ∈ D` whose
fresh path `y` has stage end index `se = se^{4096,d}_{k,d}(y; 1) ≤ ν(y)` with
`τ_{se}(y) ≤ P_* - 1`. Then
`∑_{a ∈ S} F^gd_e(r, ℓ) bw^⊗(β) exp(-z_* N^e_{P_*-1}(a)) ≤
max(b_*, (77/100)^d)^k ∑_{(r, ℓ) ∈ D} F^gd_e(r, ℓ)`. -/
theorem tsum_c3GoodMarginal_mul_exp_neg_trWhiteCount_le_stageRate (ι : FIndex)
    (hξ : IsResidueUnit ξ) (he : e ∈ bkPoints) {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (D : Set (ℕ × ℤ))
    (S : Set ((ℕ × ℤ) × List (List ℤ × ℤ))) (hS : S ⊆ trAtoms n) (hSD : ∀ a ∈ S, a.1 ∈ D)
    (hSse : ∀ a ∈ S, ∃ i s : ℕ,
      trStageEnd n ξ (epsStar : ℝ) 4096 d (trFreshPath e a) k d 1 = i ∧
        trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) i = some s ∧ s ≤ pStar ι - 1) :
    ∑' a : S, c3GoodMarginal ι n ξ e ((a.1.1.1 : ℤ), a.1.1.2) *
        ENNReal.ofReal (trListWeight a.1.2) *
        ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1)))) ≤
      ENNReal.ofReal (max (stageRate : ℝ) ((77 / 100) ^ d) ^ k) *
        ∑' x : D, c3GoodMarginal ι n ξ e ((x.1.1 : ℤ), x.1.2) := by
  have h := tsum_ofReal_mul_exp_neg_trWhiteCount_le_stageRate ι hξ he hd k
    (fun x ↦ (c3GoodMarginal ι n ξ e ((x.1 : ℤ), x.2)).toReal) D S hS hSD hSse
  have hz : (gammaStar : ℝ) = zStar := by rw [gammaStar_cast, zStar_cast]
  have hL : ∀ a : S, c3GoodMarginal ι n ξ e ((a.1.1.1 : ℤ), a.1.1.2) *
      ENNReal.ofReal (trListWeight a.1.2) *
      ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1)))) =
      ENNReal.ofReal ((c3GoodMarginal ι n ξ e ((a.1.1.1 : ℤ), a.1.1.2)).toReal *
        trListWeight a.1.2 *
        Real.exp (-((gammaStar : ℝ) * trWhiteCount n ξ e a.1 (pStar ι - 1)))) := by
    intro a
    rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (trListWeight_nonneg _)),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (c3GoodMarginal_ne_top ι _),
      hz]
  refine (le_of_eq (tsum_congr hL)).trans (h.trans_eq ?_)
  congr 1
  exact tsum_congr fun x ↦ ENNReal.ofReal_toReal (c3GoodMarginal_ne_top ι _)

/-- **Stages of the bootstrap set are completed by the schedule.** For `ι = b` and `k ∈ {2, 3}`,
let `a = ((r, ℓ), β)` with `β` live, `a ∈ Low^e(b) \ (Bad^e_m(b) ∪ Clr(b))` and no oversize hit
at any time `u ≤ p_{k-1}(b)`, where `j(e) + m = ⌊n/2⌋` and `P_*(b) ≤ ⌊n/2⌋`. Then the fresh path
`y` of `a` has stage end index `se = se^{4096,5}_{k-1,5}(y; 1) ≤ ν(y)` and
`τ_{se}(y) ≤ p_k(b) ≤ P_*(b) - 1`. -/
theorem exists_trStageEnd_b_of_noHit {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {e : ℤ × ℤ} (he : e ∈ bkPoints) {m : ℕ} (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ))
    (hP : pStar .b ≤ n / 2) {k : ℕ} (hk2 : 2 ≤ k) (hk3 : k ≤ 3)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hlive : TrLive a.2) (hlow : a ∈ trLow .b n ξ e)
    (hbad : a ∉ trBad .b n e m) (hclr : a ∉ trClear .b n)
    (hover : ∀ u ≤ schedule .b (k - 1), ¬IsTrOversizeHit .b n ξ (epsStar : ℝ) e a u) :
    ∃ i s : ℕ, trStageEnd n ξ (epsStar : ℝ) 4096 5 (trFreshPath e a) (k - 1) 5 1 = i ∧
      trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) i = some s ∧ s ≤ pStar .b - 1 := by
  have hsch : List.ofFn (fun i : Fin (rStar .b + 1) => schedule .b i) =
      [169, 15486, 514217, 63701994] := schedule_values_b
  have hs1 : schedule .b 1 = 15486 := by simpa using congrArg (fun l => l.getD 1 0) hsch
  have hs2 : schedule .b 2 = 514217 := by simpa using congrArg (fun l => l.getD 2 0) hsch
  have hs3 : schedule .b 3 = 63701994 := by simpa using congrArg (fun l => l.getD 3 0) hsch
  have ht := trStageTime_b_values
  simp only [Prod.mk.injEq] at ht
  obtain ⟨ht0, ht1, ht2⟩ := ht
  have hh := trStageHold_b_4096
  have hPb := pStar_b
  have hkP : schedule .b k ≤ pStar .b - 1 := by
    have := schedule_lt_pStar .b (by rw [rStar_b]; exact hk3 : k ≤ rStar .b)
    omega
  have hC : ∀ s < k - 1, ((trStageTime .b 4096 5 s + (5 - 1) * trStageHold .b 4096 : ℕ) : ℤ) ≤
      ((schedule .b (k - 1) : ℕ) : ℤ) := by
    intro s hs
    rw [hh]
    have : s = 0 ∨ s = 1 := by omega
    obtain rfl | rfl := this
    · rw [ht0]; interval_cases k <;> simp [hs1, hs2]
    · rw [ht1]; interval_cases k <;> simp_all
  have hHs : ∀ s < k - 1, (trStageTime .b 4096 5 (s + 1) : ℤ) ≤ ((schedule .b k : ℕ) : ℤ) := by
    intro s hs
    have : s = 0 ∨ s = 1 := by omega
    obtain rfl | rfl := this
    · rw [ht1]; interval_cases k <;> simp [hs2, hs3]
    · rw [ht2]; interval_cases k <;> simp_all
  obtain ⟨i, hi, -, t, ht, htH⟩ := trStageEnd_le_trNu_and_trStopTime_le hξ he hm hP
    (G := 4096) (d := 5) (k := k - 1) (by norm_num) (by omega) (by omega) hC hHs hlive hlow
    hbad hclr (fun u hu ↦ hover u (by exact_mod_cast hu))
  exact ⟨i, t, by exact_mod_cast hi, ht, by omega⟩

/-- The drift-free sum of a list of blocks: `∑ (4 j(βᵏ) - l(βᵏ)) = 4 ∑ j(βᵏ) - ∑ l(βᵏ)`. -/
theorem sum_map_four_mul_bkJ_sub_bkL (L : List (List ℤ × ℤ)) :
    (L.map fun b ↦ 4 * bkJ (chBlockPoint b) - bkL (chBlockPoint b)).sum =
      4 * (L.map fun b ↦ bkJ (chBlockPoint b)).sum - (L.map fun b ↦ bkL (chBlockPoint b)).sum := by
  induction L with
  | nil => simp
  | cons b L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Outside the fresh deviation event, an atom whose displacement avoids `𝓘_g` lies outside
the deviation event `Dev_{g,v}` for every `1 ≤ v ≤ min(V_* - 1, ⌊n/2⌋)`. -/
theorem notMem_c3Exceptional_of_notMem_c3FreshDev {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ trAtoms n) {g v : ℕ} (hv1 : 1 ≤ v) (hv : v ≤ min (Vstar ι - 1) (n / 2))
    (hI : ((a.1.1 : ℤ), a.1.2) ∉ c3InitEvent ι g) (hd : a ∉ c3FreshDev ι n) :
    a ∉ c3Exceptional ι n g v := by
  simp only [mem_c3FreshDev, ha, true_and, not_exists, not_and, not_or, not_le] at hd
  rw [notMem_c3Exceptional_iff ha]
  refine ⟨hI, ?_, fun u hu1 huv ↦ ?_⟩
  · exact_mod_cast (hd v hv1 hv).1
  · have h := (hd u hu1 (huv.trans hv)).2
    have h' : |((4 * ((a.2.take u).map fun b ↦ bkJ (chBlockPoint b)).sum -
        ((a.2.take u).map fun b ↦ bkL (chBlockPoint b)).sum : ℤ) : ℚ)| < 4 * Xd ι v := by
      refine lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_left (Xd_mono ι huv) (by norm_num))
      convert h using 3
      exact (sum_map_four_mul_bkJ_sub_bkL _).symm
    exact_mod_cast h'

/-- **Discounted paid mass of the low, unadvanced atoms.**
Let `ι` be a Fourier index, `ξ` a unit, `Δ ∈ 𝔗_{n,ξ,ε_*}`, `e ∈ Δ` with gap `ω = gap(e)`, and
`m ≥ D_sc(ι)` with `j(e) + m = ⌊n/2⌋`, `P_*(ι) ≤ ⌊n/2⌋` and `ς(ι, m) < ω`. Then, all constants
taken at `ι`,
`∑_{a ∈ Low^e \ Bad^e_m} μ̃_e(a) exp(-z_* N^e_{P_*-1}(a)) ≤
  Π_ad + q_mass η_{r_*} + 𝓔_sq + U_o + ε_init + q_mass (U_v + U_d + E_piece)`. -/
@[collatz_pos_dens "lem_c3_estar_mass"]
theorem tsum_trFreshLaw_trEStar_lt (ι : FIndex) (hξ : IsResidueUnit ξ) {Δ : BkTriangle}
    (hΔ : Δ ∈ bkFamily n ξ epsStar) (he : e ∈ Δ) {m : ℕ} (hm : Dsc ι ≤ m)
    (hjm : bkJ e + m = ((n / 2 : ℕ) : ℤ)) (hP : pStar ι ≤ n / 2)
    (hmω : gapSplit ι m < trGap n ξ (epsStar : ℝ) e) :
    ∑' a : (trLow ι n ξ e \ trBad ι n e m : Set _), c3PaidLaw n ξ e a *
        ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1)))) ≤
      ENNReal.ofReal ((piAd ι : ℝ) + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι + epsInit ι +
        qMass * ((Uv ι : ℝ) + Ud ι + ePiece ι)) := by
  classical
  -- the gap `ω`
  have heP : e ∈ bkPoints := BkTriangle.mem_bkPoints_of_mem he
  have hFar : (omegaFar ι : ℝ) < trGap n ξ (epsStar : ℝ) e :=
    (omegaFar_le_gapSplit_of_Dsc_le ι (by exact_mod_cast hm)).trans_lt hmω
  have hω0 : 0 ≤ trGap n ξ (epsStar : ℝ) e := trGap_nonneg _ _ _ _
  have hdomF : ∀ x, c3GoodMarginal ι n ξ e x ≤
      ENNReal.ofReal (firstPassageLaw (trGap n ξ (epsStar : ℝ) e) x) :=
    c3GoodMarginal_le_ofReal_firstPassageLaw ι
  have hblack : BkBlack n ξ (epsStar : ℝ) e :=
    (bkBlack_iff_exists_mem_bkFamily hξ epsStar_mem_bkRange.1 epsStar_mem_bkRange.2 heP).2
      ⟨Δ, hΔ, he⟩
  set ω := (trGap n ξ (epsStar : ℝ) e).toNat with hωdef
  have hωZ : (ω : ℤ) = trGap n ξ (epsStar : ℝ) e := Int.toNat_of_nonneg hω0
  have hFarω : (omegaFar ι : ℝ) < ω := by rw [← hωZ] at hFar; exact_mod_cast hFar
  have hFarN : omegaFar ι < ω := by exact_mod_cast hFarω
  have hmax := max_le_omegaFar ι
  have hω34 : 2 ^ 34 ≤ ω := (le_of_max_le_left (le_of_max_le_left hmax)).trans hFarN.le
  have hω125 : 12500000 ≤ ω := (le_of_max_le_right hmax).trans hFarN.le
  have hqm := tsum_c3PaidPassage_lt_qMass hξ heP hblack (by rw [← hωZ]; exact_mod_cast hω34)
  have hl : bkL e + (ω : ℤ) = Δ.l := by rw [hωZ, bkFamily_epsStar_l_eq_add_trGap hξ hΔ he]
  rw [← hωZ] at hdomF
  -- notation
  set N : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦
    ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1)))) with hNdef
  have hN1 : ∀ a, N a ≤ 1 := fun a ↦ by
    simp only [hNdef]
    rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (by exact_mod_cast zStar_nonneg) (trWhiteCount_nonneg _ _ _)
  set Fg : ℕ × ℤ → ℝ≥0∞ := fun x ↦ c3GoodMarginal ι n ξ e ((x.1 : ℤ), x.2) with hFg
  set Fx : ℕ × ℤ → ℝ≥0∞ := fun x ↦
    ∑' π : c3InitException ι ω, c3PaidTerm n ξ e ((x.1 : ℤ), x.2) π with hFx
  set w : List (List ℤ × ℤ) → ℝ≥0∞ := fun β ↦ ENNReal.ofReal (trListWeight β) with hw
  set fg : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦ Fg a.1 * w a.2 * N a with hfg
  set L := trLow ι n ξ e \ trBad ι n e m with hL
  have hFgq : ∑' x, Fg x ≤ ENNReal.ofReal (qMass : ℝ) :=
    ((ENNReal.tsum_le_tsum fun x ↦ c3GoodMarginal_le_c3PaidPassage ι n ξ e _).trans
      (ENNReal.tsum_comp_le_tsum_of_injective natCast_prod_injective _)).trans hqm.le
  -- splitting off the initial exception
  have hsplit : ∀ a : (ℕ × ℤ) × List (List ℤ × ℤ), c3PaidLaw n ξ e a *
      ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1)))) ≤
      Fx a.1 * w a.2 + fg a := by
    intro a
    change c3PaidLaw n ξ e a * N a ≤ _
    rw [c3PaidLaw_def, ← c3GoodMarginal_add_tsum_c3InitException ι, add_mul, add_mul, add_comm]
    exact add_le_add (mul_le_of_le_one_right zero_le (hN1 a)) le_rfl
  have hEx : ∑' a : L, Fx a.1.1 * w a.1.2 ≤ ENNReal.ofReal (epsInit ι : ℝ) := by
    have hπ : ∀ π : c3InitException ι ω,
        ∑' x : ℕ × ℤ, c3PaidTerm n ξ e ((x.1 : ℤ), x.2) π ≤ w π.1 := by
      intro π
      refine (ENNReal.tsum_comp_le_tsum_of_injective natCast_prod_injective
        (fun y ↦ c3PaidTerm n ξ e y π)).trans ?_
      simp only [c3PaidTerm]
      rw [tsum_eq_single (chBlockPath π.1 π.1.length) (fun y hy ↦ ite_eq_right (Ne.symm hy)),
        ite_eq_left rfl]
      refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (trListWeight_nonneg _) ?_)
      rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
      exact mul_nonneg (by exact_mod_cast zStar_nonneg) (trCount_nonneg _ _ _)
    calc ∑' a : L, Fx a.1.1 * w a.1.2 ≤ ∑' a : trAtoms n, Fx a.1.1 * w a.1.2 :=
          ENNReal.tsum_mono_subtype
            (fun a : (ℕ × ℤ) × List (List ℤ × ℤ) ↦ Fx a.1 * w a.2) fun a ha ↦ ha.1.1
      _ = ∑' x, Fx x := tsum_trAtoms_mul_trListWeight Fx
      _ = ∑' π : c3InitException ι ω, ∑' x : ℕ × ℤ, c3PaidTerm n ξ e ((x.1 : ℤ), x.2) π :=
          ENNReal.tsum_comm
      _ ≤ ∑' π : c3InitException ι ω, w π.1 := ENNReal.tsum_le_tsum hπ
      _ = ENNReal.ofReal (∑' π : c3InitException ι ω, trListWeight π.1) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ trListWeight_nonneg _)
            (summable_trListWeight_c3InitException ι hω125)).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ((tsum_trListWeight_c3InitException_le ι hω125).trans ?_)
          rw [cast_epsInit ι]
          have : (148 : ℝ) / ω ≤ 148 / omegaFar ι :=
            div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast omegaFar_pos ι) hFarω.le
          linarith
  -- the initial deviation set
  set I : Set (ℕ × ℤ) := {x | ((x.1 : ℤ), x.2) ∈ c3InitEvent ι ω} with hI
  have hTI : ∑' a : ({a | a ∈ L ∧ a.1 ∈ I} : Set _), fg a ≤
      ENNReal.ofReal ((Uo ι : ℝ) + (2 * (ω : ℝ)) ^ (-1 / 2 : ℝ)) := by
    calc ∑' a : ({a | a ∈ L ∧ a.1 ∈ I} : Set _), fg a
        ≤ ∑' a : ({a | a ∈ L ∧ a.1 ∈ I} : Set _), I.indicator Fg a.1.1 * w a.1.2 :=
          ENNReal.tsum_le_tsum fun a ↦ by
            rw [Set.indicator_of_mem a.2.2]
            exact mul_le_of_le_one_right zero_le (hN1 _)
      _ ≤ ∑' a : trAtoms n, I.indicator Fg a.1.1 * w a.1.2 :=
          ENNReal.tsum_mono_subtype
            (fun a : (ℕ × ℤ) × List (List ℤ × ℤ) ↦ I.indicator Fg a.1 * w a.2) fun a ha ↦ ha.1.1.1
      _ = ∑' x, I.indicator Fg x := tsum_trAtoms_mul_trListWeight _
      _ = ∑' x : I, Fg x := (_root_.tsum_subtype I Fg).symm
      _ ≤ ∑' x : I, ENNReal.ofReal (firstPassageLaw ω ((x.1.1 : ℤ), x.1.2)) :=
          ENNReal.tsum_le_tsum fun x ↦ hdomF _
      _ ≤ ∑' y : c3InitEvent ι ω, ENNReal.ofReal (firstPassageLaw ω y) :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun x : I ↦ (⟨((x.1.1 : ℤ), x.1.2), x.2⟩ : c3InitEvent ι ω))
            (fun x y hxy ↦ Subtype.ext (natCast_prod_injective (congrArg Subtype.val hxy)))
            (fun y ↦ ENNReal.ofReal (firstPassageLaw ω y.1))
      _ = ENNReal.ofReal (∑' y : c3InitEvent ι ω, firstPassageLaw ω y) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ firstPassageLaw_nonneg _ _)
            ((summable_firstPassageLaw ω).subtype _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal
          (tsum_firstPassageLaw_c3InitEvent_le ι (le_trans (by norm_num) hω34))
  -- the fresh deviation and slow clearing events
  set E' : Set (List (List ℤ × ℤ)) := {β | ((0, 0), β) ∈ c3FreshDev ι n ∪ trClear ι n} with hE'
  have hE : ∀ a : (ℕ × ℤ) × List (List ℤ × ℤ), a ∈ c3FreshDev ι n ∪ trClear ι n ↔ a.2 ∈ E' :=
    fun _ ↦ Iff.rfl
  set k : List (List ℤ × ℤ) → ℝ≥0∞ := E'.indicator w with hk
  have hUv : (0 : ℝ) ≤ (Uv ι : ℝ) + Ud ι := by
    have h1 : (0 : ℝ) < Uv ι := by exact_mod_cast Uv_pos ι
    have h2 : (0 : ℝ) < Ud ι := by exact_mod_cast Ud_pos ι
    linarith
  have hEp : (0 : ℝ) ≤ ePiece ι := by exact_mod_cast ePiece_nonneg ι
  have hkm : ∑' β : {β : List (List ℤ × ℤ) // β.length = n / 2 ∧
      ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}}, k β.1 ≤
      ENNReal.ofReal ((Uv ι : ℝ) + Ud ι + ePiece ι) := by
    calc ∑' β : {β : List (List ℤ × ℤ) // β.length = n / 2 ∧
          ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}}, k β.1
        = (∑' x : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw ω ((x.1 : ℤ), x.2))) *
          ∑' β : {β : List (List ℤ × ℤ) // β.length = n / 2 ∧
            ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}}, k β.1 := by
          rw [tsum_ofReal_firstPassageLaw_natCast, one_mul]
      _ = ∑' a : trAtoms n, ENNReal.ofReal (firstPassageLaw ω ((a.1.1.1 : ℤ), a.1.1.2)) *
          k a.1.2 := (tsum_trAtoms_mul _ _).symm
      _ ≤ ∑' a, (c3FreshDev ι n ∪ trClear ι n).indicator
          (fun a ↦ ENNReal.ofReal (trFreshLaw n e ω a)) a := by
          refine le_trans (le_of_eq (tsum_congr fun a ↦ ?_))
            (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _)
          by_cases h : a.1.2 ∈ E'
          · rw [hk, Set.indicator_of_mem h, Set.indicator_of_mem ((hE _).2 h), trFreshLaw_def,
              ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _)]
          · rw [hk, Set.indicator_of_notMem h,
              Set.indicator_of_notMem (fun h' ↦ h ((hE _).1 h')), mul_zero]
      _ = ∑' a : (c3FreshDev ι n ∪ trClear ι n : Set _), ENNReal.ofReal (trFreshLaw n e ω a) :=
          (_root_.tsum_subtype _ _).symm
      _ ≤ ∑' a : c3FreshDev ι n, ENNReal.ofReal (trFreshLaw n e ω a) +
          ∑' a : trClear ι n, ENNReal.ofReal (trFreshLaw n e ω a) :=
          ENNReal.tsum_union_le (fun a ↦ ENNReal.ofReal (trFreshLaw n e ω a)) _ _
      _ ≤ ENNReal.ofReal ((Uv ι : ℝ) + Ud ι) + ENNReal.ofReal (ePiece ι : ℝ) :=
          add_le_add (tsum_trFreshLaw_c3FreshDev_le ι n e ω) (tsum_trFreshLaw_trClear_lt ι n e ω hP)
      _ = _ := (ENNReal.ofReal_add hUv hEp).symm
  have hTE : ∑' a : (L ∩ (c3FreshDev ι n ∪ trClear ι n) : Set _), fg a ≤
      ENNReal.ofReal (qMass : ℝ) * ENNReal.ofReal ((Uv ι : ℝ) + Ud ι + ePiece ι) := by
    calc ∑' a : (L ∩ (c3FreshDev ι n ∪ trClear ι n) : Set _), fg a
        ≤ ∑' a : (L ∩ (c3FreshDev ι n ∪ trClear ι n) : Set _), Fg a.1.1 * k a.1.2 :=
          ENNReal.tsum_le_tsum fun a ↦ by
            rw [hk, Set.indicator_of_mem ((hE _).1 a.2.2)]
            exact mul_le_of_le_one_right zero_le (hN1 _)
      _ ≤ ∑' a : trAtoms n, Fg a.1.1 * k a.1.2 :=
          ENNReal.tsum_mono_subtype
            (fun a : (ℕ × ℤ) × List (List ℤ × ℤ) ↦ Fg a.1 * k a.2) fun a ha ↦ ha.1.1.1
      _ = (∑' x, Fg x) * ∑' β : {β : List (List ℤ × ℤ) // β.length = n / 2 ∧
            ∀ x ∈ β, x ∈ {b : List ℤ × ℤ | b.2 ∈ ({4, 5} : Set ℤ)}}, k β.1 :=
          tsum_trAtoms_mul _ _
      _ ≤ _ := mul_le_mul' hFgq hkm
  -- the remaining atoms
  set G : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
    {a | a ∈ L ∧ a.1 ∉ I ∧ a ∉ c3FreshDev ι n ∪ trClear ι n ∧ Fg a.1 ≠ 0 ∧
      trListWeight a.2 ≠ 0} with hG
  set hit : (ℕ × ℤ) × List (List ℤ × ℤ) → ℕ → Prop :=
    fun a u ↦ IsTrOversizeHit ι n ξ (epsStar : ℝ) e a u with hhit
  set LA : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
    {a | a ∈ G ∧ ∀ u ≤ schedule ι (rStar ι - 1), ¬hit a u} with hLA
  set Li : ℕ → Set ((ℕ × ℤ) × List (List ℤ × ℤ)) := fun i ↦
    {a | a ∈ G ∧ (0 < i → ∀ u ≤ schedule ι (i - 1), ¬hit a u) ∧ ∃ u ≤ schedule ι i, hit a u}
    with hLi
  -- survival times
  have hsurv : ∀ a ∈ G, ∀ k ≤ rStar ι, (0 < k → ∀ u ≤ schedule ι (k - 1), ¬hit a u) →
      ∃ t, trStopTime n ξ (epsStar : ℝ) (trFreshPath e a) (k + 1) = some t ∧
        t ≤ pStar ι - 1 := by
    rintro a ⟨⟨hlow, hbad⟩, -, hdc, -, hw0⟩ k hk hover
    have hlive : TrLive a.2 := (trLive_iff_prod_ne_zero _).2 (by rwa [trListWeight_def] at hw0)
    obtain ⟨-, h⟩ := le_trNu_and_trStopTime_le_schedule hξ heP hjm hP hk hlive hlow hbad
      (fun h ↦ hdc (Or.inr h)) hover
    obtain ⟨t, ht, htle⟩ := h (k + 1) (by omega) le_rfl
    refine ⟨t, ht, htle.trans ?_⟩
    have := schedule_lt_pStar ι hk
    simp only [Nat.add_sub_cancel]
    omega
  -- the cover
  have hcover : L ⊆ {a | a ∈ L ∧ a.1 ∈ I} ∪ (L ∩ (c3FreshDev ι n ∪ trClear ι n)) ∪
      {a | fg a = 0} ∪ LA ∪ ⋃ i ∈ range (rStar ι), Li i := by
    intro a ha
    by_cases hI' : a.1 ∈ I
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨ha, hI'⟩)))
    by_cases hd : a ∈ c3FreshDev ι n ∪ trClear ι n
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨ha, hd⟩)))
    by_cases hz : fg a = 0
    · exact Or.inl (Or.inl (Or.inr hz))
    have hF0 : Fg a.1 ≠ 0 := fun h ↦ hz (by simp only [hfg, h, zero_mul])
    have hw0 : trListWeight a.2 ≠ 0 := fun h ↦ hz (by
      simp only [hfg, hw, h, ENNReal.ofReal_zero, mul_zero, zero_mul])
    have hGa : a ∈ G := ⟨ha, hI', hd, hF0, hw0⟩
    by_cases hA : ∀ u ≤ schedule ι (rStar ι - 1), ¬hit a u
    · exact Or.inl (Or.inr ⟨hGa, hA⟩)
    push Not at hA
    have hex : ∃ i, ∃ u ≤ schedule ι i, hit a u :=
      let ⟨u, hu, h⟩ := hA; ⟨rStar ι - 1, u, hu, h⟩
    refine Or.inr (Set.mem_biUnion (x := Nat.find hex) ?_ ⟨hGa, fun hpos u hu h ↦ ?_,
      Nat.find_spec hex⟩)
    · obtain ⟨u, hu, h⟩ := hA
      have := Nat.find_min' hex ⟨u, hu, h⟩
      simp only [coe_range, Set.mem_Iio]
      have := rStar_pos ι
      omega
    · exact Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex) ⟨u, hu, h⟩
  have hTZ : ∑' a : ({a | fg a = 0} : Set _), fg a = 0 := ENNReal.tsum_eq_zero.2 fun a ↦ a.2
  -- the discount of a class: `η_k` for atoms without an oversize hit up to `p_{k-1}`
  have hclass : ∀ κ ≤ rStar ι, ∀ (D : Set (ℕ × ℤ)) (S : Set ((ℕ × ℤ) × List (List ℤ × ℤ))),
      S ⊆ G → (∀ a ∈ S, a.1 ∈ D) → (∀ a ∈ S, 0 < κ → ∀ u ≤ schedule ι (κ - 1), ¬hit a u) →
      ∑' a : S, fg a ≤ ENNReal.ofReal (eventCoeff ι κ : ℝ) * ∑' x : D, Fg x := by
    intro κ hk D S hSG hSD hSo
    have hSA : S ⊆ trAtoms n := fun a ha ↦ (hSG ha).1.1.1
    by_cases hb : ι = .b ∧ 2 ≤ κ
    · obtain ⟨rfl, hk2⟩ := hb
      have h := tsum_c3GoodMarginal_mul_exp_neg_trWhiteCount_le_stageRate .b hξ heP
        (d := 5) (by norm_num) (κ - 1) D S hSA hSD fun a ha ↦ by
          obtain ⟨⟨hlow, hbad⟩, -, hdc, -, hw0⟩ := hSG ha
          have hlive : TrLive a.2 :=
            (trLive_iff_prod_ne_zero _).2 (by rwa [trListWeight_def] at hw0)
          exact exists_trStageEnd_b_of_noHit hξ heP hjm hP hk2 (by simpa using hk) hlive hlow
            hbad (fun h ↦ hdc (Or.inr h)) (hSo a ha (by omega))
      have hmax : max (stageRate : ℝ) ((77 / 100) ^ 5) = stageRate := by
        have := congrArg (fun q : ℚ ↦ (q : ℝ)) max_stageRate_pow_five
        push_cast at this
        exact this
      have hη : ((eventCoeff .b κ : ℚ) : ℝ) = (stageRate : ℝ) ^ (κ - 1) := by
        rw [rStar_b] at hk
        interval_cases κ <;> simp
      rw [hmax, ← hη] at h
      exact h
    · have hη : eventCoeff ι κ = thetaEn κ := by
        cases ι with
        | o => rfl
        | b =>
          have : κ = 0 ∨ κ = 1 := by
            by_contra h
            exact hb ⟨rfl, by omega⟩
          obtain rfl | rfl := this
          · simp
          · rw [eventCoeff_b_one, thetaEn_eq]; norm_num
      rw [hη]
      exact tsum_c3GoodMarginal_mul_exp_neg_trWhiteCount_le ι hξ heP κ D S hSA hSD
        fun a ha ↦ hsurv a (hSG ha) κ hk (hSo a ha)
  -- the atoms without an early oversize hit
  have hTA : ∑' a : LA, fg a ≤
      ENNReal.ofReal (eventCoeff ι (rStar ι) : ℝ) * ENNReal.ofReal (qMass : ℝ) := by
    refine (hclass (rStar ι) le_rfl Set.univ LA (fun a ha ↦ ha.1) (fun _ _ ↦ trivial)
      (fun a ha _ ↦ ha.2)).trans ?_
    gcongr
    exact (tsum_univ (f := Fg)).trans_le hFgq
  -- the atoms with a first oversize hit in the window `(p_{i-1}, p_i]`
  set Bp : ℕ → ℝ := fun i ↦ 2 * (Xd ι (schedule ι i) : ℝ) +
    8 / 25 * totalAllowance ι (schedule ι i) + 1 + Hpack ι with hBpdef
  set Aa : ℕ → ℝ := fun i ↦
    (bAn : ℝ) * (sStar ι i : ℝ) - totalAllowance ι (schedule ι i) - 1 with hAadef
  set P : ℕ → ℝ := fun i ↦
    ((qPack : ℝ) * (127 / 40 * (2 * (Xd ι (schedule ι i) : ℝ) + 1) +
          totalAllowance ι (schedule ι i)) +
        127 / 40 * (Hpack ι * (qPack : ℝ) + (Gammapk : ℝ) / 4)) / Aa i with hPdef
  set Q : ℕ → ℝ := fun i ↦
    49 / 120 * ((4 * (qPack : ℝ) * Bp i + Gammapk) * (1 + 127 / 40 * Bp i / Aa i) / √(ω : ℝ))
    with hQdef
  have hTi : ∀ i ∈ range (rStar ι), ∑' a : Li i, fg a ≤
      ENNReal.ofReal (eventCoeff ι i : ℝ) * ENNReal.ofReal (P i + Q i) := by
    intro i hi
    rw [mem_range] at hi
    have hvi : schedule ι i ≤ n / 2 := (schedule_lt_pStar ι hi.le).le.trans hP
    have hbig : Li i ⊆ c3Big n ξ epsStar e (schedule ι i) (sStar ι i : ℝ) := by
      rintro a ⟨hGa, hno, u, hu, Δ', hΔ', hmem, hs⟩
      refine ⟨hGa.1.1.1, u, hu, Δ', hΔ', hmem, le_trans ?_ hs⟩
      have : traceIndex ι u = i := by
        refine (traceIndex_eq_iff ι (hu.trans (schedule_monotone ι hi.le))).2
          ⟨hi.le, hu, fun j hj ↦ ?_⟩
        by_contra hju
        exact hno (by omega) u ((not_lt.1 hju).trans (schedule_monotone ι (by omega)))
          ⟨Δ', hΔ', hmem, hs⟩
      rw [betaStar_def ι, this]
    have hgW : (ω : ℝ) / 32 + (Xd ι (schedule ι i) : ℝ) + (Xl ι (schedule ι i) : ℝ) / 4 +
        alpha * (totalAllowance ι (schedule ι i) : ℝ) + 1 ≤ ω * drift := by
      have := two_mul_rpow_add_mul_alpha_add_one_le_mul_drift ι (schedule_lt_Vstar ι hi) hFarω.le
      linarith
    set U := c3AnchorCols ι (bkFamily n ξ epsStar) e Δ (schedule ι i) (sStar ι i : ℝ) with hU
    have hD : ∀ a ∈ Li i, a.1 ∈ {x : ℕ × ℤ | (x.1 : ℤ) ∈ U} := by
      intro a ha
      obtain ⟨⟨haL, hI', hd, hF0, hw0⟩, -⟩ := id ha
      have hat : a ∈ trAtoms n := haL.1.1
      have h1 : 1 ≤ schedule ι i := le_trans (pInit_pos ι) (pInit_le_schedule ι i)
      have hex : a ∉ c3Exceptional ι n ω (schedule ι i) :=
        notMem_c3Exceptional_of_notMem_c3FreshDev hat h1
          (le_min (by have := schedule_lt_Vstar ι hi; omega) hvi) hI' (fun h ↦ hd (Or.inl h))
      have hμ : trFreshLaw n e ω a ≠ 0 := by
        rw [trFreshLaw_def]
        refine mul_ne_zero (fun h0 ↦ hF0 ?_) hw0
        have := hdomF ((a.1.1 : ℤ), a.1.2)
        rw [h0, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
        exact this
      exact exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional_epsStar hξ hΔ he hl
        hgW hμ (hbig ha) hex
    have hBA : 2 * (Xd ι (schedule ι i) : ℝ) + 8 / 25 * totalAllowance ι (schedule ι i) + 1 +
        Hpack ι ≤
        5 / 16 * ((bAn : ℝ) * (sStar ι i : ℝ) - totalAllowance ι (schedule ι i) - 1) := by
      have h := packWidth_add_Hpack_le ι i
      rw [packWidth_def, aStar_def] at h
      have h' := (Rat.cast_le (K := ℝ)).2 h
      push_cast at h'
      exact h'
    refine (hclass i hi.le _ _ (fun a ha ↦ ha.1) hD (fun a ha ↦ ha.2.1)).trans ?_
    gcongr
    refine le_trans ?_ (BkBlack.tsum_tsum_c3GoodMarginal_c3AnchorCols_le ι hblack hξ heP hωZ hω34 Δ
      (schedule ι i) (by exact_mod_cast sStar_pos ι i) hBA)
    calc _ ≤ ∑' p : U × ℤ, c3GoodMarginal ι n ξ e ((p.1 : ℤ), p.2) :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (f := fun x : {x : ℕ × ℤ | (x.1 : ℤ) ∈ U} ↦ ((⟨(x.1.1 : ℤ), x.2⟩ : U), x.1.2))
            (fun x y hxy ↦ by
              simp only [Prod.mk.injEq, Subtype.mk.injEq, Nat.cast_inj] at hxy
              exact Subtype.ext (Prod.ext hxy.1 hxy.2))
            (fun p ↦ c3GoodMarginal ι n ξ e ((p.1 : ℤ), p.2))
      _ = _ := ENNReal.tsum_prod (f := fun (r : U) (ℓ : ℤ) ↦ c3GoodMarginal ι n ξ e ((r : ℤ), ℓ))
  -- the real quantities
  have hθ (i : ℕ) : (0 : ℝ) ≤ eventCoeff ι i := by exact_mod_cast eventCoeff_nonneg ι i
  have hq : (0 : ℝ) < qPack := by exact_mod_cast qPack_pos
  have hΓ : (0 : ℝ) < Gammapk := by exact_mod_cast Gammapk_pos
  have hqm0 : (0 : ℝ) < qMass := by exact_mod_cast qMass_pos
  have hR0 : (0 : ℝ) < ROmega ι := by exact_mod_cast ROmega_pos ι
  have hsq : (ROmega ι : ℝ) ≤ √(ω : ℝ) := by
    rw [show (ROmega ι : ℝ) = √((ROmega ι : ℝ) ^ 2) from (Real.sqrt_sq hR0.le).symm]
    exact Real.sqrt_le_sqrt (by rw [← cast_omegaFar ι]; exact hFarω.le)
  have hsq0 : 0 < √(ω : ℝ) := hR0.trans_le hsq
  have hXW (i : ℕ) : (0 : ℝ) < Xd ι (schedule ι i) ∧ (0 : ℝ) ≤ totalAllowance ι (schedule ι i) := by
    refine ⟨by exact_mod_cast Xd_pos ι _, ?_⟩
    exact_mod_cast (totalAllowance_pos ι _).le
  have hA (i : ℕ) : 0 < Aa i := by
    have := aStar_pos ι i
    rw [aStar_def] at this
    simp only [hAadef]
    exact_mod_cast this
  have hBp (i : ℕ) : 0 ≤ Bp i := by
    obtain ⟨h1, h2⟩ := hXW i
    have : (0 : ℝ) ≤ Hpack ι := Nat.cast_nonneg _
    simp only [hBpdef]
    linarith
  have hc (i : ℕ) : 0 ≤ (4 * (qPack : ℝ) * Bp i + Gammapk) * (1 + 127 / 40 * Bp i / Aa i) := by
    have h1 : 0 ≤ 4 * (qPack : ℝ) * Bp i := mul_nonneg (by linarith) (hBp i)
    have h2 : 0 ≤ 127 / 40 * Bp i / Aa i := div_nonneg (by linarith [hBp i]) (hA i).le
    exact mul_nonneg (by linarith) (by linarith)
  have hPQ (i : ℕ) : 0 ≤ P i + Q i := by
    obtain ⟨h1, h2⟩ := hXW i
    have h3 : 0 ≤ (qPack : ℝ) * (127 / 40 * (2 * (Xd ι (schedule ι i) : ℝ) + 1) +
      totalAllowance ι (schedule ι i)) := mul_nonneg hq.le (by linarith)
    have h4 : (0 : ℝ) ≤ Hpack ι * (qPack : ℝ) := mul_nonneg (Nat.cast_nonneg _) hq.le
    exact add_nonneg (div_nonneg (by linarith) (hA i).le)
      (mul_nonneg (by norm_num) (div_nonneg (hc i) hsq0.le))
  have hpi : (piAd ι : ℝ) = ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) * P i := by
    rw [piAd_def ι]
    push_cast
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [hPdef, hAadef, cStar_def, aStar_def]
    push_cast
    ring
  have hEsq : (2 * (ω : ℝ)) ^ (-1 / 2 : ℝ) + ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) * Q i ≤
      Esq ι := by
    have h1 : (2 * (ω : ℝ)) ^ (-1 / 2 : ℝ) ≤ 1 / ROmega ι := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by positivity),
        ← Real.sqrt_eq_rpow, one_div]
      refine inv_anti₀ hR0 (hsq.trans (Real.sqrt_le_sqrt (by linarith)))
    have h2 : ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) * Q i ≤
        ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) *
        (49 / 120 * ((4 * (qPack : ℝ) * Bp i + Gammapk) * (1 + 127 / 40 * Bp i / Aa i) /
          ROmega ι)) := by
      refine sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (hc i) hR0 hsq) (by norm_num))
        (hθ i)
    have h3 : (Esq ι : ℝ) = 1 / ROmega ι + ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) *
        (49 / 120 * ((4 * (qPack : ℝ) * Bp i + Gammapk) * (1 + 127 / 40 * Bp i / Aa i) /
          ROmega ι)) := by
      rw [Esq_def ι]
      push_cast
      rw [add_div, add_comm, mul_sum, sum_div]
      congr 1
      refine sum_congr rfl fun i _ ↦ ?_
      simp only [hBpdef, hAadef, thinPackRatio_def, packWidth_def, aStar_def]
      push_cast
      ring
    rw [h3]
    linarith
  have hreal : (epsInit ι : ℝ) + ((Uo ι : ℝ) + (2 * (ω : ℝ)) ^ (-1 / 2 : ℝ) +
      qMass * ((Uv ι : ℝ) + Ud ι + ePiece ι) + eventCoeff ι (rStar ι) * qMass +
      ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) * (P i + Q i)) ≤
      (piAd ι : ℝ) + qMass * eventCoeff ι (rStar ι) + Esq ι + Uo ι + epsInit ι +
        qMass * ((Uv ι : ℝ) + Ud ι + ePiece ι) := by
    have hs : ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) * (P i + Q i) =
        ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) * P i +
          ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) * Q i := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ ↦ mul_add _ _ _
    rw [hs, ← hpi, mul_comm (eventCoeff ι (rStar ι) : ℝ)]
    linarith
  -- assembling
  have h0 : (0 : ℝ) ≤ (Uo ι : ℝ) + (2 * (ω : ℝ)) ^ (-1 / 2 : ℝ) :=
    add_nonneg (by exact_mod_cast (Uo_pos ι).le) (by positivity)
  have hU3 : (0 : ℝ) ≤ (Uv ι : ℝ) + Ud ι + ePiece ι := add_nonneg hUv hEp
  have hterm : ∀ i ∈ range (rStar ι), (0 : ℝ) ≤ eventCoeff ι i * (P i + Q i) :=
    fun i _ ↦ mul_nonneg (hθ i) (hPQ i)
  calc ∑' a : L, c3PaidLaw n ξ e a *
        ENNReal.ofReal (Real.exp (-((zStar : ℝ) * trWhiteCount n ξ e a (pStar ι - 1))))
      ≤ ∑' a : L, (Fx a.1.1 * w a.1.2 + fg a) := ENNReal.tsum_le_tsum fun a ↦ hsplit a
    _ = ∑' a : L, Fx a.1.1 * w a.1.2 + ∑' a : L, fg a := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (epsInit ι : ℝ) +
        (ENNReal.ofReal ((Uo ι : ℝ) + (2 * (ω : ℝ)) ^ (-1 / 2 : ℝ)) +
          ENNReal.ofReal (qMass : ℝ) * ENNReal.ofReal ((Uv ι : ℝ) + Ud ι + ePiece ι) + 0 +
          ENNReal.ofReal (eventCoeff ι (rStar ι) : ℝ) * ENNReal.ofReal (qMass : ℝ) +
          ∑ i ∈ range (rStar ι),
            ENNReal.ofReal (eventCoeff ι i : ℝ) * ENNReal.ofReal (P i + Q i)) := by
      refine add_le_add hEx ?_
      calc ∑' a : L, fg a ≤ ∑' a : ({a | a ∈ L ∧ a.1 ∈ I} ∪ (L ∩ (c3FreshDev ι n ∪ trClear ι n)) ∪
            {a | fg a = 0} ∪ LA ∪ ⋃ i ∈ range (rStar ι), Li i : Set _), fg a :=
            ENNReal.tsum_mono_subtype fg hcover
        _ ≤ ∑' a : ({a | a ∈ L ∧ a.1 ∈ I} : Set _), fg a +
              ∑' a : (L ∩ (c3FreshDev ι n ∪ trClear ι n) : Set _), fg a +
              ∑' a : ({a | fg a = 0} : Set _), fg a + ∑' a : LA, fg a +
              ∑' a : (⋃ i ∈ range (rStar ι), Li i : Set _), fg a :=
            (ENNReal.tsum_union_le _ _ _).trans (add_le_add ((ENNReal.tsum_union_le _ _ _).trans
              (add_le_add ((ENNReal.tsum_union_le _ _ _).trans
                (add_le_add (ENNReal.tsum_union_le _ _ _) le_rfl)) le_rfl)) le_rfl)
        _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add hTI hTE) hTZ.le) hTA)
            ((ENNReal.tsum_biUnion_le _ _ _).trans (sum_le_sum hTi))
    _ = ENNReal.ofReal ((epsInit ι : ℝ) + ((Uo ι : ℝ) + (2 * (ω : ℝ)) ^ (-1 / 2 : ℝ) +
          qMass * ((Uv ι : ℝ) + Ud ι + ePiece ι) + eventCoeff ι (rStar ι) * qMass +
          ∑ i ∈ range (rStar ι), (eventCoeff ι i : ℝ) * (P i + Q i))) := by
      rw [add_zero, ENNReal.ofReal_add (by exact_mod_cast (epsInit_pos ι).le)
          (add_nonneg (add_nonneg (add_nonneg h0 (mul_nonneg hqm0.le hU3))
            (mul_nonneg (hθ _) hqm0.le)) (sum_nonneg hterm)),
        ENNReal.ofReal_add (add_nonneg (add_nonneg h0 (mul_nonneg hqm0.le hU3))
            (mul_nonneg (hθ _) hqm0.le)) (sum_nonneg hterm),
        ENNReal.ofReal_add (add_nonneg h0 (mul_nonneg hqm0.le hU3)) (mul_nonneg (hθ _) hqm0.le),
        ENNReal.ofReal_add h0 (mul_nonneg hqm0.le hU3), ENNReal.ofReal_mul hqm0.le,
        ENNReal.ofReal_mul (hθ _), ENNReal.ofReal_sum_of_nonneg hterm]
      congr 2
      exact sum_congr rfl fun i _ ↦ (ENNReal.ofReal_mul (hθ i)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end CollatzPosDens
