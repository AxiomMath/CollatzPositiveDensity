/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3NarrowTable
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Bounds for short exponential sums near odd dyadic angles

For every pair `(s, t)` in the index set `T'` of the table `c3NarrowTable` of upper bounds
`U'_{s,t}`, every odd integer `b` and every real `β` with `|β| ≤ 10⁻⁶`,
`‖∑_{m<t} exp(2πi (2^m - 1)(b + β)/2^s)‖ ≤ t U'_{s,t}`.

Write `x_m = 2π (2^m - 1)(b + β)/2^s`. The squared norm of `∑_m exp(i x_m)` is the double sum
`∑_{j,k<t} cos(x_k - x_j)`. Split `x_k - x_j = X + Y` with `X = 2π (2^k - 2^j) b / 2^s` and
`Y = 2π (2^k - 2^j) β / 2^s`. Since `cos` is `1`-Lipschitz, `cos(X + Y) ≤ cos X + |Y|`, and
`|Y| ≤ 2 · 3.1416 · 10⁻⁶ |2^k - 2^j| / 2^s`. The angle `X` is an integer multiple of `π / 128`,
determined modulo `2π` by the residue of `(2^k - 2^j) b 2^(8-s)` modulo `256`; in particular it
depends only on `b` modulo `2^s`. Each `cos(π r / 128)`, `0 ≤ r < 256`, is bounded above by an
explicit rational: by symmetry it suffices to bound `cos(π k / 128)` and `sin(π k / 128)` above
and below for `k ≤ 32`, which follows from monotonicity, the enclosure
`3.14159265358979323846 < π < 3.14159265358979323847`, and Taylor's theorem with remainder
`13 / (12! · 12)` on `[-1, 1]`. This reduces each of the `20` pairs other than `(1, 2)` to a
finite exact rational comparison over the odd residues `b` modulo `2^s`, checked by kernel
evaluation. For the pair `(1, 2)` the squared norm is `2 - 2 cos(π β) ≤ (π β)^2`.

## Main results

* `CollatzPosDens.norm_sum_exp_le_c3NarrowTable`: the narrow cell estimate
  `‖∑_{m<t} exp(2πi (2^m - 1)(b + β)/2^s)‖ ≤ t U'_{s,t}` on `T'`.
* `CollatzPosDens.C3NarrowCells.norm_sum_exp_mul_I_sq`: the squared norm of a sum of unimodular
  exponentials as a double sum of cosines.
* `CollatzPosDens.C3NarrowCells.abs_cos_sub_cosTaylor_le`,
  `CollatzPosDens.C3NarrowCells.abs_sin_sub_sinTaylor_le`: Taylor bounds for `cos` and `sin` on
  `[-1, 1]`.

## Implementation notes

Mazur's argument perturbs the normalized square `f(θ) = t⁻² ‖∑ e(a_m θ)‖²` by the mean value
theorem, with `|f'| ≤ 4π t⁻² ∑_{i<m} (a_m - a_i) < 13 t⁻² ∑_{i<m} (a_m - a_i)`. Here the same
quantity is perturbed termwise through the Lipschitz bound for `cos`, with `2π < 6.2832` in place
of `4π < 13` on the ordered double sum; the resulting bound is slightly stronger. The values at the
centres are bounded through a table of rational bounds for `cos(π k / 128)` and `sin(π k / 128)`,
`k ≤ 32`, obtained from Taylor polynomials of degree `10` and `11`, instead of degree-`24` Taylor
polynomials at each centre. Every finite check is evaluated by the kernel in `ℤ` after clearing
denominators (`cosUpperTable_check_int`, `check_of_int`), never in `ℚ`; the cell checks use the
symmetries `j ↔ k` and `b ↦ 2^s - b` of the angle index. The bound `|β| ≤ 10⁻⁶` is written
`1 / 10 ^ 6`, the sum over `m < t` runs over `Finset.range t.toNat`, and `2^s` is an integer power,
matching the integer indexing of `c3NarrowTable`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

namespace C3NarrowCells

open Real Complex Finset

/-- The degree-`10` Taylor polynomial of `cos` at `0`. -/
def cosTaylor {K : Type*} [Field K] (x : K) : K :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 - x ^ 10 / 3628800

/-- The degree-`11` Taylor polynomial of `sin` at `0`. -/
def sinTaylor {K : Type*} [Field K] (x : K) : K :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 - x ^ 11 / 39916800

/-- The rational Taylor polynomial `cosTaylor q`, cast to `ℝ`, is `cosTaylor (q : ℝ)`. -/
@[simp, norm_cast]
lemma ratCast_cosTaylor (q : ℚ) : ((cosTaylor q : ℚ) : ℝ) = cosTaylor (q : ℝ) := by
  simp [cosTaylor]

/-- The rational Taylor polynomial `sinTaylor q`, cast to `ℝ`, is `sinTaylor (q : ℝ)`. -/
@[simp, norm_cast]
lemma ratCast_sinTaylor (q : ℚ) : ((sinTaylor q : ℚ) : ℝ) = sinTaylor (q : ℝ) := by
  simp [sinTaylor]

/-- The first twelve terms of the exponential series at `x i`, split into real and imaginary
parts. -/
lemma sum_range_twelve_ofReal_mul_I (x : ℝ) :
    ∑ m ∈ range 12, ((x : ℂ) * I) ^ m / (m.factorial : ℂ) =
      ((cosTaylor x : ℝ) : ℂ) + ((sinTaylor x : ℝ) : ℂ) * I := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_pow]
  simp [pow_succ, Complex.I_mul_I, Nat.factorial, cosTaylor, sinTaylor]
  ring

/-- Taylor's bound for `cos`: on `[-1, 1]` the degree-`10` Taylor polynomial is within
`13 / (12! * 12)` of `cos`. -/
lemma abs_cos_sub_cosTaylor_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x - cosTaylor x| ≤ 13 / 5748019200 := by
  have h := Complex.exp_bound (x := (x : ℂ) * I) (by simpa using hx) (n := 12) (by norm_num)
  rw [sum_range_twelve_ofReal_mul_I] at h
  have hre : Real.cos x - cosTaylor x =
      (Complex.exp (x * I) - (((cosTaylor x : ℝ) : ℂ) + ((sinTaylor x : ℝ) : ℂ) * I)).re := by
    simp [Complex.exp_ofReal_mul_I_re]
  have hn : ‖(x : ℂ) * I‖ = |x| := by simp
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (h.trans ?_)
  rw [hn]
  have : |x| ^ 12 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  norm_num [Nat.factorial] at this ⊢
  linarith

/-- Taylor's bound for `sin`: on `[-1, 1]` the degree-`11` Taylor polynomial is within
`13 / (12! * 12)` of `sin`. -/
lemma abs_sin_sub_sinTaylor_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - sinTaylor x| ≤ 13 / 5748019200 := by
  have h := Complex.exp_bound (x := (x : ℂ) * I) (by simpa using hx) (n := 12) (by norm_num)
  rw [sum_range_twelve_ofReal_mul_I] at h
  have him : Real.sin x - sinTaylor x =
      (Complex.exp (x * I) - (((cosTaylor x : ℝ) : ℂ) + ((sinTaylor x : ℝ) : ℂ) * I)).im := by
    simp [Complex.exp_ofReal_mul_I_im]
  have hn : ‖(x : ℂ) * I‖ = |x| := by simp
  rw [him]
  refine (Complex.abs_im_le_norm _).trans (h.trans ?_)
  rw [hn]
  have : |x| ^ 12 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  norm_num [Nat.factorial] at this ⊢
  linarith

/-- Upper bounds `cos (π k / 128) ≤ cosUpperTable k / 10¹⁵` for `k ≤ 32`. -/
def cosUpperTable : List ℤ :=
  [1000000002261649, 999698820957853, 998795458466822, 997290458940339, 995184728933846,
   992479536860359, 989176512226430, 985277644650590, 980785282664880, 975702132300178,
   970031255456193, 963776068057089, 956940337993857, 949528182854684, 941544067444664,
   932992801096375, 923879534772908, 914209757965122, 903989295384977, 893224303456944,
   881921266609596, 870086993369628, 857728612260641, 844853567509174, 831469614560558,
   817584815407299, 803207533732796, 788346429873319, 773010455601281, 757208848732936,
   740951127563751, 724247085134791, 707106783333574]

/-- Lower bounds `cosLowerTable k / 10¹⁵ ≤ cos (π k / 128)` for `k ≤ 32`. -/
def cosLowerTable : List ℤ :=
  [999999997738351, 999698816434555, 998795453943523, 997290454417041, 995184724410548,
   992479532337061, 989176507703132, 985277640127292, 980785278141581, 975702127776879,
   970031250932895, 963776063533790, 956940333470559, 949528178331385, 941544062921366,
   932992796573077, 923879530249610, 914209753441823, 903989290861679, 893224298933646,
   881921262086298, 870086988846330, 857728607737343, 844853562985876, 831469610037260,
   817584810884001, 803207529209497, 788346425350020, 773010451077982, 757208844209638,
   740951123040453, 724247080611492, 707106778810276]

/-- Upper bounds `sin (π k / 128) ≤ sinUpperTable k / 10¹⁵` for `k ≤ 32`. -/
def sinUpperTable : List ℤ :=
  [2261649, 24541230784561, 49067676589067, 73564565861317, 98017142591210, 122410677460865,
   146730476717011, 170961891021950, 195090324277777, 219101242418519, 242980182164913,
   266712759736548, 290284679516112, 313681742660541, 336889855653869, 359895038796637,
   382683434626738, 405241316266637, 427555095691927, 449611331916248, 471396739087631,
   492898194491404, 514102746454818, 534997622148652, 555570235281087, 575808193679214,
   595699306753616, 615231592841514, 634393286424073, 653172845213498, 671558957105673,
   689540546994130, 707106783441269]

/-- Lower bounds `sinLowerTable k / 10¹⁵ ≤ sin (π k / 128)` for `k ≤ 32`. -/
def sinLowerTable : List ℤ :=
  [-2261649, 24541226261263, 49067672065769, 73564561338018, 98017138067911,
   122410672937567, 146730472193713, 170961886498652, 195090319754479, 219101237895221,
   242980177641615, 266712755213249, 290284674992813, 313681738137242, 336889851130571,
   359895034273339, 382683430103440, 405241311743339, 427555091168629, 449611327392950,
   471396734564333, 492898189968106, 514102741931519, 534997617625353, 555570230757788,
   575808189155916, 595699302230318, 615231588318216, 634393281900774, 653172840690200,
   671558952582374, 689540542470832, 707106778917970]

/-- The numerator of `cosTaylor (N / D)` over the common denominator `10! D¹⁰`. -/
def cosPolyZ (N D : ℤ) : ℤ :=
  3628800 * D ^ 10 - 1814400 * N ^ 2 * D ^ 8 + 151200 * N ^ 4 * D ^ 6 - 5040 * N ^ 6 * D ^ 4 +
    90 * N ^ 8 * D ^ 2 - N ^ 10

/-- The numerator of `sinTaylor (N / D)` over the common denominator `11! D¹¹`. -/
def sinPolyZ (N D : ℤ) : ℤ :=
  39916800 * N * D ^ 10 - 6652800 * N ^ 3 * D ^ 8 + 332640 * N ^ 5 * D ^ 6 -
    7920 * N ^ 7 * D ^ 4 + 110 * N ^ 9 * D ^ 2 - N ^ 11

/-- `cosTaylor (N / D)` as the quotient of `cosPolyZ N D` by `10! D¹⁰`. -/
lemma cosTaylor_intCast_div (N D : ℤ) (hD : D ≠ 0) :
    cosTaylor ((N : ℚ) / D) = (cosPolyZ N D : ℚ) / ((3628800 * D ^ 10 : ℤ) : ℚ) := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  rw [eq_div_iff (by push_cast; positivity)]
  simp only [cosTaylor, cosPolyZ]
  push_cast
  field_simp
  ring

/-- `sinTaylor (N / D)` as the quotient of `sinPolyZ N D` by `11! D¹¹`. -/
lemma sinTaylor_intCast_div (N D : ℤ) (hD : D ≠ 0) :
    sinTaylor ((N : ℚ) / D) = (sinPolyZ N D : ℚ) / ((39916800 * D ^ 11 : ℤ) : ℚ) := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  rw [eq_div_iff (by push_cast; positivity)]
  simp only [sinTaylor, sinPolyZ]
  push_cast
  field_simp
  ring

/-- An upper table check `A / B + 13 / (12! · 12) ≤ T / 10¹⁵` from its cleared-denominator
integer form. -/
lemma add_le_of_int {A B T : ℤ} (hB : 0 < B)
    (h : (A * 5748019200 + B * 13) * 10 ^ 15 ≤ T * (B * 5748019200)) :
    (A : ℚ) / B + 13 / 5748019200 ≤ (T : ℚ) / 10 ^ 15 := by
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  rw [div_add_div _ _ hB'.ne' (by norm_num), div_le_div_iff₀ (by positivity) (by norm_num)]
  exact_mod_cast h

/-- A lower table check `T / 10¹⁵ ≤ A / B - 13 / (12! · 12)` from its cleared-denominator
integer form. -/
lemma le_sub_of_int {A B T : ℤ} (hB : 0 < B)
    (h : T * (B * 5748019200) ≤ (A * 5748019200 - B * 13) * 10 ^ 15) :
    (T : ℚ) / 10 ^ 15 ≤ (A : ℚ) / B - 13 / 5748019200 := by
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  rw [div_sub_div _ _ hB'.ne' (by norm_num), div_le_div_iff₀ (by norm_num) (by positivity)]
  exact_mod_cast h

/-- The integer form of `cosUpperTable_check`, with `π k / 128 ≥ k · 314159265358979323846 /
(128 · 10²⁰)`. -/
lemma cosUpperTable_check_int : ∀ k : ℕ, k < 33 →
    (cosPolyZ (k * 314159265358979323846) 12800000000000000000000 * 5748019200 +
        3628800 * 12800000000000000000000 ^ 10 * 13) * 10 ^ 15 ≤
      cosUpperTable.getD k 0 * (3628800 * 12800000000000000000000 ^ 10 * 5748019200) := by
  decide +kernel

/-- The integer form of `cosLowerTable_check`. -/
lemma cosLowerTable_check_int : ∀ k : ℕ, k < 33 →
    cosLowerTable.getD k 0 * (3628800 * 12800000000000000000000 ^ 10 * 5748019200) ≤
      (cosPolyZ (k * 314159265358979323847) 12800000000000000000000 * 5748019200 -
        3628800 * 12800000000000000000000 ^ 10 * 13) * 10 ^ 15 := by
  decide +kernel

/-- The integer form of `sinUpperTable_check`. -/
lemma sinUpperTable_check_int : ∀ k : ℕ, k < 33 →
    (sinPolyZ (k * 314159265358979323847) 12800000000000000000000 * 5748019200 +
        39916800 * 12800000000000000000000 ^ 11 * 13) * 10 ^ 15 ≤
      sinUpperTable.getD k 0 * (39916800 * 12800000000000000000000 ^ 11 * 5748019200) := by
  decide +kernel

/-- The integer form of `sinLowerTable_check`. -/
lemma sinLowerTable_check_int : ∀ k : ℕ, k < 33 →
    sinLowerTable.getD k 0 * (39916800 * 12800000000000000000000 ^ 11 * 5748019200) ≤
      (sinPolyZ (k * 314159265358979323846) 12800000000000000000000 * 5748019200 -
        39916800 * 12800000000000000000000 ^ 11 * 13) * 10 ^ 15 := by
  decide +kernel

/-- The angle `k · p / 10²⁰ / 128` as a quotient of integers. -/
lemma natCast_mul_div_eq_intCast_div (k : ℕ) {p : ℚ} {P : ℤ} (hP : (P : ℚ) = p) :
    (k : ℚ) * (p / 10 ^ 20) / 128 =
      (((k : ℤ) * P : ℤ) : ℚ) / ((12800000000000000000000 : ℤ) : ℚ) := by
  rw [← hP]; push_cast; ring

/-- The table `cosUpperTable` dominates the Taylor upper bound at the lower end of the
enclosure of `π k / 128`. -/
lemma cosUpperTable_check : ∀ k : ℕ, k < 33 →
    cosTaylor ((k : ℚ) * (314159265358979323846 / 10 ^ 20) / 128) + 13 / 5748019200 ≤
      (cosUpperTable.getD k 0 : ℚ) / 10 ^ 15 := by
  intro k hk
  rw [natCast_mul_div_eq_intCast_div k (P := 314159265358979323846) (by norm_num),
    cosTaylor_intCast_div _ _ (by norm_num)]
  exact add_le_of_int (by norm_num) (cosUpperTable_check_int k hk)

/-- The table `cosLowerTable` is dominated by the Taylor lower bound at the upper end of the
enclosure of `π k / 128`. -/
lemma cosLowerTable_check : ∀ k : ℕ, k < 33 → (cosLowerTable.getD k 0 : ℚ) / 10 ^ 15 ≤
    cosTaylor ((k : ℚ) * (314159265358979323847 / 10 ^ 20) / 128) - 13 / 5748019200 := by
  intro k hk
  rw [natCast_mul_div_eq_intCast_div k (P := 314159265358979323847) (by norm_num),
    cosTaylor_intCast_div _ _ (by norm_num)]
  exact le_sub_of_int (by norm_num) (cosLowerTable_check_int k hk)

/-- The table `sinUpperTable` dominates the Taylor upper bound at the upper end of the
enclosure of `π k / 128`. -/
lemma sinUpperTable_check : ∀ k : ℕ, k < 33 →
    sinTaylor ((k : ℚ) * (314159265358979323847 / 10 ^ 20) / 128) + 13 / 5748019200 ≤
      (sinUpperTable.getD k 0 : ℚ) / 10 ^ 15 := by
  intro k hk
  rw [natCast_mul_div_eq_intCast_div k (P := 314159265358979323847) (by norm_num),
    sinTaylor_intCast_div _ _ (by norm_num)]
  exact add_le_of_int (by norm_num) (sinUpperTable_check_int k hk)

/-- The table `sinLowerTable` is dominated by the Taylor lower bound at the lower end of the
enclosure of `π k / 128`. -/
lemma sinLowerTable_check : ∀ k : ℕ, k < 33 → (sinLowerTable.getD k 0 : ℚ) / 10 ^ 15 ≤
    sinTaylor ((k : ℚ) * (314159265358979323846 / 10 ^ 20) / 128) - 13 / 5748019200 := by
  intro k hk
  rw [natCast_mul_div_eq_intCast_div k (P := 314159265358979323846) (by norm_num),
    sinTaylor_intCast_div _ _ (by norm_num)]
  exact le_sub_of_int (by norm_num) (sinLowerTable_check_int k hk)

/-- The lower end of the twenty-digit enclosure of `π`. -/
lemma piLo_lt_pi : (314159265358979323846 / 10 ^ 20 : ℝ) < π :=
  lt_of_eq_of_lt (by norm_num) Real.pi_gt_d20

/-- The upper end of the twenty-digit enclosure of `π`. -/
lemma pi_lt_piHi : π < (314159265358979323847 / 10 ^ 20 : ℝ) :=
  lt_of_lt_of_eq Real.pi_lt_d20 (by norm_num)

/-- `cos (π k / 128) ≤ cosUpperTable k / 10¹⁵` for `k ≤ 32`. -/
lemma cos_le_cosUpperTable {k : ℕ} (hk : k ≤ 32) :
    Real.cos (π * k / 128) ≤ (cosUpperTable.getD k 0 : ℝ) / 10 ^ 15 := by
  have hpl := piLo_lt_pi
  have hk' : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  set y : ℝ := (k : ℝ) * (314159265358979323846 / 10 ^ 20) / 128 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : |y| ≤ 1 := by rw [abs_of_nonneg hy0, hy]; nlinarith
  have h1 : Real.cos (π * k / 128) ≤ Real.cos y :=
    Real.cos_le_cos_of_nonneg_of_le_pi hy0 (by nlinarith [Real.pi_pos]) (by rw [hy]; nlinarith)
  have h2 := (abs_le.1 (abs_cos_sub_cosTaylor_le hy1)).2
  have h3 : cosTaylor y + 13 / 5748019200 ≤ (cosUpperTable.getD k 0 : ℝ) / 10 ^ 15 := by
    have h := (Rat.cast_le (K := ℝ)).2 (cosUpperTable_check k (by omega))
    push_cast at h
    rw [hy]; exact h
  linarith

/-- `cosLowerTable k / 10¹⁵ ≤ cos (π k / 128)` for `k ≤ 32`. -/
lemma cosLowerTable_le_cos {k : ℕ} (hk : k ≤ 32) :
    (cosLowerTable.getD k 0 : ℝ) / 10 ^ 15 ≤ Real.cos (π * k / 128) := by
  have hph := pi_lt_piHi
  have hk' : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  set y : ℝ := (k : ℝ) * (314159265358979323847 / 10 ^ 20) / 128 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : |y| ≤ 1 := by rw [abs_of_nonneg hy0, hy]; nlinarith
  have h1 : Real.cos y ≤ Real.cos (π * k / 128) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by rw [hy]; nlinarith [Real.pi_gt_three])
      (by rw [hy]; nlinarith)
  have h2 := (abs_le.1 (abs_cos_sub_cosTaylor_le hy1)).1
  have h3 : (cosLowerTable.getD k 0 : ℝ) / 10 ^ 15 ≤ cosTaylor y - 13 / 5748019200 := by
    have h := (Rat.cast_le (K := ℝ)).2 (cosLowerTable_check k (by omega))
    push_cast at h
    rw [hy]; exact h
  linarith

/-- `sin (π k / 128) ≤ sinUpperTable k / 10¹⁵` for `k ≤ 32`. -/
lemma sin_le_sinUpperTable {k : ℕ} (hk : k ≤ 32) :
    Real.sin (π * k / 128) ≤ (sinUpperTable.getD k 0 : ℝ) / 10 ^ 15 := by
  have hph := pi_lt_piHi
  have hk' : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  set y : ℝ := (k : ℝ) * (314159265358979323847 / 10 ^ 20) / 128 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : |y| ≤ 1 := by rw [abs_of_nonneg hy0, hy]; nlinarith
  have h1 : Real.sin (π * k / 128) ≤ Real.sin y :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos])
      (by rw [hy]; nlinarith [Real.pi_gt_three]) (by rw [hy]; nlinarith)
  have h2 := (abs_le.1 (abs_sin_sub_sinTaylor_le hy1)).2
  have h3 : sinTaylor y + 13 / 5748019200 ≤ (sinUpperTable.getD k 0 : ℝ) / 10 ^ 15 := by
    have h := (Rat.cast_le (K := ℝ)).2 (sinUpperTable_check k (by omega))
    push_cast at h
    rw [hy]; exact h
  linarith

/-- `sinLowerTable k / 10¹⁵ ≤ sin (π k / 128)` for `k ≤ 32`. -/
lemma sinLowerTable_le_sin {k : ℕ} (hk : k ≤ 32) :
    (sinLowerTable.getD k 0 : ℝ) / 10 ^ 15 ≤ Real.sin (π * k / 128) := by
  have hpl := piLo_lt_pi
  have hk' : (k : ℝ) ≤ 32 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  set y : ℝ := (k : ℝ) * (314159265358979323846 / 10 ^ 20) / 128 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : |y| ≤ 1 := by rw [abs_of_nonneg hy0, hy]; nlinarith
  have h1 : Real.sin y ≤ Real.sin (π * k / 128) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos]) (by rw [hy]; nlinarith)
  have h2 := (abs_le.1 (abs_sin_sub_sinTaylor_le hy1)).1
  have h3 : (sinLowerTable.getD k 0 : ℝ) / 10 ^ 15 ≤ sinTaylor y - 13 / 5748019200 := by
    have h := (Rat.cast_le (K := ℝ)).2 (sinLowerTable_check k (by omega))
    push_cast at h
    rw [hy]; exact h
  linarith

/-- An upper bound (times `10¹⁵`) for `cos (π q / 128)`, `q ≤ 64`. -/
def cosUpper (q : ℕ) : ℤ :=
  if q ≤ 32 then cosUpperTable.getD q 0 else sinUpperTable.getD (64 - q) 0

/-- A lower bound (times `10¹⁵`) for `cos (π q / 128)`, `q ≤ 64`. -/
def cosLower (q : ℕ) : ℤ :=
  if q ≤ 32 then cosLowerTable.getD q 0 else sinLowerTable.getD (64 - q) 0

/-- `cos (π q / 128) = sin (π (64 - q) / 128)` for `q ≤ 64`. -/
lemma cos_eq_sin_sub {q : ℕ} (hq : q ≤ 64) :
    Real.cos (π * q / 128) = Real.sin (π * ((64 - q : ℕ) : ℝ) / 128) := by
  rw [← Real.sin_pi_div_two_sub, Nat.cast_sub hq]
  congr 1
  push_cast
  ring

/-- `cos (π q / 128) ≤ cosUpper q / 10¹⁵` for `q ≤ 64`. -/
lemma cos_le_cosUpper {q : ℕ} (hq : q ≤ 64) :
    Real.cos (π * q / 128) ≤ (cosUpper q : ℝ) / 10 ^ 15 := by
  unfold cosUpper
  split_ifs with h
  · exact cos_le_cosUpperTable h
  · rw [cos_eq_sin_sub hq]
    exact sin_le_sinUpperTable (by omega)

/-- `cosLower q / 10¹⁵ ≤ cos (π q / 128)` for `q ≤ 64`. -/
lemma cosLower_le_cos {q : ℕ} (hq : q ≤ 64) :
    (cosLower q : ℝ) / 10 ^ 15 ≤ Real.cos (π * q / 128) := by
  unfold cosLower
  split_ifs with h
  · exact cosLowerTable_le_cos h
  · rw [cos_eq_sin_sub hq]
    exact sinLowerTable_le_sin (by omega)

/-- An upper bound (times `10¹⁵`) for `cos (π r / 128)`, `r < 256`. -/
def cosNum (r : ℕ) : ℤ :=
  if r ≤ 64 then cosUpper r
  else if r ≤ 128 then -cosLower (128 - r)
  else if r ≤ 192 then -cosLower (r - 128)
  else cosUpper (256 - r)

/-- `cos (π r / 128) ≤ cosNum r / 10¹⁵` for `r < 256`. -/
lemma cos_le_cosNum {r : ℕ} (hr : r < 256) :
    Real.cos (π * r / 128) ≤ (cosNum r : ℝ) / 10 ^ 15 := by
  unfold cosNum
  split_ifs with h1 h2 h3
  · exact cos_le_cosUpper h1
  · have := cosLower_le_cos (q := 128 - r) (by omega)
    have e : Real.cos (π * r / 128) = -Real.cos (π * ((128 - r : ℕ) : ℝ) / 128) := by
      rw [← Real.cos_pi_sub, Nat.cast_sub (by omega)]
      congr 1; push_cast; ring
    rw [e]; push_cast; linarith
  · have := cosLower_le_cos (q := r - 128) (by omega)
    have e : Real.cos (π * r / 128) = -Real.cos (π * ((r - 128 : ℕ) : ℝ) / 128) := by
      rw [← Real.cos_add_pi, Nat.cast_sub (by omega)]
      congr 1; push_cast; ring
    rw [e]; push_cast; linarith
  · have := cos_le_cosUpper (q := 256 - r) (by omega)
    have e : Real.cos (π * r / 128) = Real.cos (π * ((256 - r : ℕ) : ℝ) / 128) := by
      rw [← Real.cos_two_pi_sub, Nat.cast_sub (by omega)]
      congr 1; push_cast; ring
    rw [e]; exact this

/-- The squared norm of a sum of unimodular exponentials, expanded as a double sum of
cosines of the phase differences. -/
lemma norm_sum_exp_mul_I_sq {ι : Type*} (F : Finset ι) (x : ι → ℝ) :
    ‖∑ k ∈ F, Complex.exp (x k * I)‖ ^ 2 = ∑ j ∈ F, ∑ k ∈ F, Real.cos (x k - x j) := by
  rw [Complex.sq_norm, ← Complex.ofReal_re (normSq _), ← Complex.mul_conj, map_sum,
    Finset.sum_mul_sum, Complex.re_sum]
  simp_rw [Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : (x k : ℂ) * I + (starRingEnd ℂ) ((x j : ℂ) * I) = ((x k - x j : ℝ) : ℂ) * I := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- The residue class mod `256` of `(2^k - 2^j) b 2^(8-s)`, the numerator of the angle
`2π (2^k - 2^j) b / 2^s` in units of `π / 128`. -/
def angleIndex (s : ℕ) (b : ℤ) (j k : ℕ) : ℕ :=
  ((((2 : ℤ) ^ k - 2 ^ j) * b * 2 ^ (8 - s)) % 256).toNat

/-- The angle index is a residue modulo `256`. -/
lemma angleIndex_lt (s : ℕ) (b : ℤ) (j k : ℕ) : angleIndex s b j k < 256 := by
  unfold angleIndex; omega

/-- The angle index depends only on `b` modulo `2^s`. -/
lemma angleIndex_emod {s : ℕ} (hs : s ≤ 8) (b : ℤ) (j k : ℕ) :
    angleIndex s (b % 2 ^ s) j k = angleIndex s b j k := by
  unfold angleIndex
  congr 1
  have h256 : (2 : ℤ) ^ s * 2 ^ (8 - s) = 256 := by
    rw [← pow_add, Nat.add_sub_cancel' hs]; norm_num
  conv_rhs => rw [← Int.emod_add_mul_ediv b (2 ^ s)]
  have : ((2 : ℤ) ^ k - 2 ^ j) * (b % 2 ^ s + 2 ^ s * (b / 2 ^ s)) * 2 ^ (8 - s) =
      ((2 : ℤ) ^ k - 2 ^ j) * (b % 2 ^ s) * 2 ^ (8 - s) +
        (((2 : ℤ) ^ k - 2 ^ j) * (b / 2 ^ s)) * 256 := by
    rw [← h256]; ring
  rw [this, Int.add_mul_emod_self_right]

/-- `cos (2π (2^k - 2^j) b / 2^s) = cos (π r / 128)` for the angle index `r`. -/
lemma cos_eq_cos_angleIndex {s : ℕ} (hs : s ≤ 8) (b : ℤ) (j k : ℕ) :
    Real.cos (2 * π * ((2 : ℝ) ^ k - 2 ^ j) * b / 2 ^ s) =
      Real.cos (π * (angleIndex s b j k : ℝ) / 128) := by
  set n : ℤ := ((2 : ℤ) ^ k - 2 ^ j) * b * 2 ^ (8 - s) with hn
  have h256 : (2 : ℝ) ^ s * 2 ^ (8 - s) = 256 := by
    rw [← pow_add, Nat.add_sub_cancel' hs]; norm_num
  have hcast : ((angleIndex s b j k : ℕ) : ℝ) = ((n % 256 : ℤ) : ℝ) := by
    have : ((angleIndex s b j k : ℕ) : ℤ) = n % 256 :=
      Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))
    exact_mod_cast this
  have e1 : (n : ℝ) = ((n % 256 : ℤ) : ℝ) + 256 * ((n / 256 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv n 256).symm
  have e2 : (n : ℝ) = ((2 : ℝ) ^ k - 2 ^ j) * b * 2 ^ (8 - s) := by rw [hn]; push_cast; ring
  have hs0 : (2 : ℝ) ^ s ≠ 0 := by positivity
  have harg : 2 * π * ((2 : ℝ) ^ k - 2 ^ j) * b / 2 ^ s =
      π * ((n % 256 : ℤ) : ℝ) / 128 + ((n / 256 : ℤ) : ℝ) * (2 * π) := by
    have : ((n % 256 : ℤ) : ℝ) = ((2 : ℝ) ^ k - 2 ^ j) * b * 2 ^ (8 - s) -
        256 * ((n / 256 : ℤ) : ℝ) := by linarith
    have h' : (2 : ℝ) ^ (8 - s) = 256 / 2 ^ s := by rw [eq_div_iff hs0, mul_comm, h256]
    rw [this, h']
    field_simp
    ring
  rw [harg, Real.cos_add_int_mul_two_pi, hcast]

/-- The `m`-th summand as the exponential of a real phase times `i`. -/
lemma exp_two_pi_I_eq (s m : ℕ) (b : ℤ) (β : ℝ) :
    Complex.exp (2 * π * I * ((2 ^ m - 1) * ((b + β) / 2 ^ s))) =
      Complex.exp (((2 * π * ((2 : ℝ) ^ m - 1) * (b + β) / 2 ^ s : ℝ) : ℂ) * I) := by
  congr 1
  push_cast
  ring

/-- The cell estimate in squared form: the squared norm of the exponential sum is bounded by
the tabulated cosines at the centre plus a Lipschitz term in `β`. -/
lemma norm_sum_sq_le (s t : ℕ) (hs : s ≤ 8) (b : ℤ) {β : ℝ} (hβ : |β| ≤ (1 / 10 ^ 6)) :
    ‖∑ m ∈ range t, Complex.exp (2 * π * I * ((2 ^ m - 1) * ((b + β) / 2 ^ s)))‖ ^ 2 ≤
      (((∑ j ∈ range t, ∑ k ∈ range t, (cosNum (angleIndex s b j k) : ℚ)) / 10 ^ 15 +
        2 * (31416 / 10000) / 10 ^ 6 / 2 ^ s *
          ∑ j ∈ range t, ∑ k ∈ range t, ((|(2 : ℤ) ^ k - 2 ^ j| : ℤ) : ℚ) : ℚ) : ℝ) := by
  simp_rw [exp_two_pi_I_eq]
  rw [norm_sum_exp_mul_I_sq]
  push_cast
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  set X : ℝ := 2 * π * ((2 : ℝ) ^ k - 2 ^ j) * b / 2 ^ s
  set Y : ℝ := 2 * π * ((2 : ℝ) ^ k - 2 ^ j) * β / 2 ^ s
  have hs0 : (0 : ℝ) < 2 ^ s := by positivity
  have hXY : 2 * π * ((2 : ℝ) ^ k - 1) * (b + β) / 2 ^ s -
      2 * π * ((2 : ℝ) ^ j - 1) * (b + β) / 2 ^ s = X + Y := by
    simp only [X, Y]; field_simp; ring
  rw [hXY]
  have h1 : Real.cos (X + Y) ≤ Real.cos X + |Y| := by
    have := abs_cos_sub_cos_le (X + Y) X
    rw [add_sub_cancel_left] at this
    linarith [le_abs_self (Real.cos (X + Y) - Real.cos X)]
  have h2 : Real.cos X ≤ (cosNum (angleIndex s b j k) : ℝ) / 10 ^ 15 := by
    simp only [X]
    rw [cos_eq_cos_angleIndex hs]
    exact cos_le_cosNum (angleIndex_lt s b j k)
  have h3 : |Y| ≤ 2 * (31416 / 10000) / 10 ^ 6 / 2 ^ s * |(2 : ℝ) ^ k - 2 ^ j| := by
    simp only [Y]
    rw [abs_div, abs_of_pos hs0, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [div_le_iff₀ hs0]
    have hpi := Real.pi_lt_d4
    have ha := abs_nonneg ((2 : ℝ) ^ k - 2 ^ j)
    have hb := abs_nonneg β
    have hpi0 := Real.pi_pos
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hβ ha, mul_nonneg ha hb]
  linarith

/-- The cell estimate for a pair `(s, t)` with `1 ≤ s ≤ 8`, reduced to a finite check over the
odd residues `b` modulo `2^s`. -/
lemma norm_sum_le_of_check (s t : ℕ) (hs1 : 1 ≤ s) (hs : s ≤ 8) (U : ℚ) (hU : 0 ≤ U)
    (hcheck : ∀ b : ℕ, b < 2 ^ s → b % 2 = 1 →
      (∑ j ∈ range t, ∑ k ∈ range t, (cosNum (angleIndex s b j k) : ℚ)) / 10 ^ 15 +
        2 * (31416 / 10000) / 10 ^ 6 / 2 ^ s *
          ∑ j ∈ range t, ∑ k ∈ range t, ((|(2 : ℤ) ^ k - 2 ^ j| : ℤ) : ℚ) ≤ (t * U) ^ 2)
    {b : ℤ} (hb : Odd b) {β : ℝ} (hβ : |β| ≤ (1 / 10 ^ 6)) :
    ‖∑ m ∈ range t, Complex.exp (2 * π * I * ((2 ^ m - 1) * ((b + β) / 2 ^ s)))‖ ≤
      t * (U : ℝ) := by
  have h := norm_sum_sq_le s t hs b hβ
  have hpos : (0 : ℤ) < 2 ^ s := by positivity
  set b' : ℕ := (b % 2 ^ s).toNat with hb'
  have hb'eq : (b' : ℤ) = b % 2 ^ s := Int.toNat_of_nonneg (Int.emod_nonneg b hpos.ne')
  have hb'lt : b' < 2 ^ s := by
    have := Int.emod_lt_of_pos b hpos
    have h2 : ((2 ^ s : ℕ) : ℤ) = 2 ^ s := by push_cast; rfl
    omega
  have hb'odd : b' % 2 = 1 := by
    have h2 : (2 : ℤ) ∣ 2 ^ s := dvd_pow_self 2 (by omega)
    have := Int.emod_emod_of_dvd b h2
    have hodd := Int.odd_iff.1 hb
    omega
  have hidx : ∀ j k, angleIndex s b j k = angleIndex s (b' : ℤ) j k := fun j k => by
    rw [hb'eq, angleIndex_emod hs]
  simp_rw [hidx] at h
  have hc := hcheck b' hb'lt hb'odd
  have hc' : (((∑ j ∈ range t, ∑ k ∈ range t, (cosNum (angleIndex s (b' : ℤ) j k) : ℚ)) /
      10 ^ 15 + 2 * (31416 / 10000) / 10 ^ 6 / 2 ^ s *
        ∑ j ∈ range t, ∑ k ∈ range t, ((|(2 : ℤ) ^ k - 2 ^ j| : ℤ) : ℚ) : ℚ) : ℝ) ≤
      (((t * U) ^ 2 : ℚ) : ℝ) := by exact_mod_cast hc
  have hsq := h.trans hc'
  push_cast at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- A double sum of a symmetric function: the diagonal plus twice the strictly ordered part. -/
lemma sum_range_sum_range_of_symm {f : ℕ → ℕ → ℤ} (hf : ∀ j k, f j k = f k j) (t : ℕ) :
    ∑ j ∈ range t, ∑ k ∈ range t, f j k =
      ∑ j ∈ range t, f j j + 2 * ∑ k ∈ range t, ∑ j ∈ range k, f j k := by
  induction t with
  | zero => simp
  | succ t ih =>
    simp only [sum_range_succ, sum_add_distrib, ih]
    rw [sum_congr rfl fun x _ => hf t x]
    ring

/-- Swapping `j` and `k` negates the angle index modulo `256`. -/
lemma angleIndex_comm (s : ℕ) (b : ℤ) (j k : ℕ) :
    angleIndex s b k j = (256 - angleIndex s b j k) % 256 := by
  unfold angleIndex
  rw [show ((2 : ℤ) ^ j - 2 ^ k) * b * 2 ^ (8 - s) =
    -(((2 : ℤ) ^ k - 2 ^ j) * b * 2 ^ (8 - s)) by ring]
  generalize ((2 : ℤ) ^ k - 2 ^ j) * b * 2 ^ (8 - s) = n
  omega

/-- Replacing `b` by `2^s - b` negates the angle index modulo `256`. -/
lemma angleIndex_two_pow_sub {s : ℕ} (hs : s ≤ 8) (b : ℤ) (j k : ℕ) :
    angleIndex s (2 ^ s - b) j k = (256 - angleIndex s b j k) % 256 := by
  unfold angleIndex
  have h256 : (2 : ℤ) ^ s * 2 ^ (8 - s) = 256 := by
    rw [← pow_add, Nat.add_sub_cancel' hs]; norm_num
  rw [show ((2 : ℤ) ^ k - 2 ^ j) * (2 ^ s - b) * 2 ^ (8 - s) =
    ((2 : ℤ) ^ k - 2 ^ j) * (2 ^ s * 2 ^ (8 - s)) - ((2 : ℤ) ^ k - 2 ^ j) * b * 2 ^ (8 - s) by
      ring, h256]
  generalize ((2 : ℤ) ^ k - 2 ^ j) * b * 2 ^ (8 - s) = n
  generalize (2 : ℤ) ^ k - 2 ^ j = m
  omega

/-- `cosNum` is even modulo `256`, as `cos` is. -/
lemma cosNum_neg : ∀ r : ℕ, r < 256 → cosNum ((256 - r) % 256) = cosNum r := by
  decide +kernel

/-- The finite check of `norm_sum_le_of_check` for `U = u / 10⁶`, from a cleared-denominator
integer form that uses the symmetries `j ↔ k` and `b ↦ 2^s - b` of the angle index, so that only
the ordered pairs `j < k` and the residues `b ≤ 2^(s-1)` are evaluated. -/
lemma check_of_int (s t : ℕ) (hs1 : 1 ≤ s) (hs : s ≤ 8) (U : ℚ) (u B : ℤ) (hU : U = u / 10 ^ 6)
    (hB : ∑ j ∈ range t, ∑ k ∈ range t, |(2 : ℤ) ^ k - 2 ^ j| = B)
    (h : ∀ b : ℕ, b < 2 ^ (s - 1) + 1 → b % 2 = 1 →
      (∑ j ∈ range t, cosNum (angleIndex s b j j) +
          2 * ∑ k ∈ range t, ∑ j ∈ range k, cosNum (angleIndex s b j k)) * 2 ^ s +
          6283200000 * B ≤ (t : ℤ) ^ 2 * u ^ 2 * 1000 * 2 ^ s) :
    ∀ b : ℕ, b < 2 ^ s → b % 2 = 1 →
      (∑ j ∈ range t, ∑ k ∈ range t, (cosNum (angleIndex s b j k) : ℚ)) / 10 ^ 15 +
        2 * (31416 / 10000) / 10 ^ 6 / 2 ^ s *
          ∑ j ∈ range t, ∑ k ∈ range t, ((|(2 : ℤ) ^ k - 2 ^ j| : ℤ) : ℚ) ≤ (t * U) ^ 2 := by
  have hsym : ∀ b : ℤ, ∑ j ∈ range t, ∑ k ∈ range t, cosNum (angleIndex s b j k) =
      ∑ j ∈ range t, cosNum (angleIndex s b j j) +
        2 * ∑ k ∈ range t, ∑ j ∈ range k, cosNum (angleIndex s b j k) := fun b =>
    sum_range_sum_range_of_symm (fun j k => by
      rw [angleIndex_comm, cosNum_neg _ (angleIndex_lt s b k j)]) t
  have h2 : 2 ^ s = 2 * 2 ^ (s - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hs1]
  intro b hb hodd
  have key : (∑ j ∈ range t, ∑ k ∈ range t, cosNum (angleIndex s b j k)) * 2 ^ s +
      6283200000 * B ≤ (t : ℤ) ^ 2 * u ^ 2 * 1000 * 2 ^ s := by
    by_cases hb2 : b < 2 ^ (s - 1) + 1
    · rw [hsym]; exact h b hb2 hodd
    · have hb' : ((2 ^ s - b : ℕ) : ℤ) = 2 ^ s - b := by push_cast [Nat.cast_sub hb.le]; ring
      have e : ∀ j k, cosNum (angleIndex s b j k) = cosNum (angleIndex s (2 ^ s - b : ℕ) j k) :=
        fun j k => by
          rw [hb', angleIndex_two_pow_sub hs, cosNum_neg _ (angleIndex_lt s b j k)]
      simp_rw [e]
      rw [hsym]
      exact h _ (by omega) (by omega)
  have hq := (Int.cast_le (R := ℚ)).2 key
  simp only [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast] at hq
  rw [hU]
  generalize (∑ j ∈ range t, ∑ k ∈ range t, (cosNum (angleIndex s b j k) : ℚ)) = A at hq ⊢
  simp only [← Int.cast_sum, hB]
  have hP : (0 : ℚ) < 2 ^ s := by positivity
  generalize (2 : ℚ) ^ s = P at hq hP ⊢
  rw [show A / 10 ^ 15 + 2 * (31416 / 10000) / 10 ^ 6 / P * B =
      (A * P + 6283200000 * B) / (10 ^ 15 * P) by field_simp; ring,
    show ((t : ℚ) * (u / 10 ^ 6)) ^ 2 = (t ^ 2 * u ^ 2 * 1000 * P) / (10 ^ 15 * P) by
      field_simp; ring]
  exact div_le_div_of_nonneg_right hq (by positivity)

/-- The pair `(1, 2)`: the sum is `1 - exp(π i β)`, of norm at most `π |β|`. -/
lemma norm_sum_le_one_two {b : ℤ} (hb : Odd b) {β : ℝ} (hβ : |β| ≤ (1 / 10 ^ 6)) :
    ‖∑ m ∈ range 2, Complex.exp (2 * π * I * ((2 ^ m - 1) * ((b + β) / 2 ^ 1)))‖ ≤
      2 * ((1 / 2 ^ 16 : ℚ) : ℝ) := by
  simp_rw [exp_two_pi_I_eq]
  have hsq := norm_sum_exp_mul_I_sq (range 2)
    (fun m => 2 * π * ((2 : ℝ) ^ m - 1) * (b + β) / 2 ^ 1)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_self, Real.cos_zero] at hsq
  obtain ⟨c, rfl⟩ := hb
  have e1 : Real.cos (2 * π * ((2 : ℝ) ^ 1 - 1) * (((2 * c + 1 : ℤ) : ℝ) + β) / 2 ^ 1 -
      2 * π * ((2 : ℝ) ^ 0 - 1) * (((2 * c + 1 : ℤ) : ℝ) + β) / 2 ^ 1) = -Real.cos (π * β) := by
    rw [← Real.cos_add_pi, ← Real.cos_add_int_mul_two_pi (π * β + π) c]
    congr 1; push_cast; ring
  have e2 : Real.cos (2 * π * ((2 : ℝ) ^ 0 - 1) * (((2 * c + 1 : ℤ) : ℝ) + β) / 2 ^ 1 -
      2 * π * ((2 : ℝ) ^ 1 - 1) * (((2 * c + 1 : ℤ) : ℝ) + β) / 2 ^ 1) = -Real.cos (π * β) := by
    rw [← Real.cos_neg, ← e1]; congr 1; ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsq ⊢
  rw [e1, e2] at hsq
  have hcos := Real.one_sub_sq_div_two_le_cos (x := π * β)
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hβ2 : β ^ 2 ≤ (1 / 10 ^ 6) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg β) hβ 2
  have hle : ‖Complex.exp (((2 * π * ((2 : ℝ) ^ 0 - 1) * (((2 * c + 1 : ℤ) : ℝ) + β) / 2 ^ 1 :
      ℝ) : ℂ) * I) + Complex.exp (((2 * π * ((2 : ℝ) ^ 1 - 1) * (((2 * c + 1 : ℤ) : ℝ) + β) /
      2 ^ 1 : ℝ) : ℂ) * I)‖ ^ 2 ≤ (2 * ((1 / 2 ^ 16 : ℚ) : ℝ)) ^ 2 := by
    rw [hsq]
    have : (π * β) ^ 2 ≤ 10 * (1 / 10 ^ 12) := by
      rw [mul_pow]
      have : π ^ 2 ≤ 10 := by nlinarith
      have h0 : 0 ≤ β ^ 2 := sq_nonneg β
      calc π ^ 2 * β ^ 2 ≤ 10 * (1 / 10 ^ 6) ^ 2 := by gcongr
        _ = 10 * (1 / 10 ^ 12) := by norm_num
    push_cast
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

/-- Transfer of a cell estimate stated with natural indices to the integer-indexed table. -/
lemma of_cell {s t : ℕ} {U : ℚ} (hU : c3NarrowTable s t = U)
    (h : ∀ b : ℤ, Odd b → ∀ β : ℝ, |β| ≤ 1 / 10 ^ 6 →
      ‖∑ m ∈ range t, Complex.exp (2 * π * I * ((2 ^ m - 1) * ((b + β) / 2 ^ s)))‖ ≤
        t * (U : ℝ))
    {b : ℤ} (hb : Odd b) {β : ℝ} (hβ : |β| ≤ 1 / 10 ^ 6) :
    ‖∑ m ∈ range (t : ℤ).toNat,
        Complex.exp (2 * π * I * ((2 ^ m - 1) * ((b + β) / (2 : ℂ) ^ (s : ℤ))))‖ ≤
      ((t : ℤ) : ℝ) * (c3NarrowTable s t : ℝ) := by
  simp only [zpow_natCast, Int.toNat_natCast, Int.cast_natCast, hU]
  exact h b hb β hβ

end C3NarrowCells

open C3NarrowCells Real

/-- **Narrow cells.** For every `(s, t) ∈ T'`, every odd integer `b` and every real `β` with
`|β| ≤ 10⁻⁶`, `‖∑_{m<t} exp(2πi (2^m - 1)(b + β)/2^s)‖ ≤ t U'_{s,t}`. -/
@[collatz_pos_dens "lem_c3_narrow_cells"]
theorem norm_sum_exp_le_c3NarrowTable {s t : ℤ} (hst : (s, t) ∈ c3NarrowTableDomain) {b : ℤ}
    (hb : Odd b) {β : ℝ} (hβ : |β| ≤ 1 / 10 ^ 6) :
    ‖∑ m ∈ Finset.range t.toNat,
        Complex.exp (2 * π * Complex.I * ((2 ^ m - 1) * ((b + β) / (2 : ℂ) ^ s)))‖ ≤
      t * c3NarrowTable s t := by
  obtain ⟨hs1, -, ht2, -⟩ := mem_c3NarrowTableDomain_bounds hst
  lift s to ℕ using (by omega)
  lift t to ℕ using (by omega)
  simp only [c3NarrowTableDomain, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hst
  rcases hst with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨rfl, rfl⟩ : s = 1 ∧ t = 2 := by omega
    exact of_cell (U := 1 / 2 ^ 16) rfl
      (fun _ hb _ hβ => norm_sum_le_one_two hb hβ) hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 1 ∧ t = 3 := by omega
    exact of_cell (U := 333340 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 1 3 (by norm_num) (by norm_num) (333340 / 1000000)
        (by norm_num) (check_of_int 1 3 (by norm_num) (by norm_num) _ 333340 12
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 1 ∧ t = 4 := by omega
    exact of_cell (U := 500010 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 1 4 (by norm_num) (by norm_num) (500010 / 1000000)
        (by norm_num) (check_of_int 1 4 (by norm_num) (by norm_num) _ 500010 46
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 2 ∧ t = 2 := by omega
    exact of_cell (U := 707108 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 2 2 (by norm_num) (by norm_num) (707108 / 1000000)
        (by norm_num) (check_of_int 2 2 (by norm_num) (by norm_num) _ 707108 2
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 2 ∧ t = 3 := by omega
    exact of_cell (U := 333337 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 2 3 (by norm_num) (by norm_num) (333337 / 1000000)
        (by norm_num) (check_of_int 2 3 (by norm_num) (by norm_num) _ 333337 12
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 2 ∧ t = 4 := by omega
    exact of_cell (U := 353560 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 2 4 (by norm_num) (by norm_num) (353560 / 1000000)
        (by norm_num) (check_of_int 2 4 (by norm_num) (by norm_num) _ 353560 46
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 3 ∧ t = 2 := by omega
    exact of_cell (U := 923880 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 3 2 (by norm_num) (by norm_num) (923880 / 1000000)
        (by norm_num) (check_of_int 3 2 (by norm_num) (by norm_num) _ 923880 2
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 3 ∧ t = 3 := by omega
    exact of_cell (U := 577352 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 3 3 (by norm_num) (by norm_num) (577352 / 1000000)
        (by norm_num) (check_of_int 3 3 (by norm_num) (by norm_num) _ 577352 12
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 3 ∧ t = 4 := by omega
    exact of_cell (U := 461943 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 3 4 (by norm_num) (by norm_num) (461943 / 1000000)
        (by norm_num) (check_of_int 3 4 (by norm_num) (by norm_num) _ 461943 46
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 4 ∧ t = 2 := by omega
    exact of_cell (U := 980786 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 4 2 (by norm_num) (by norm_num) (980786 / 1000000)
        (by norm_num) (check_of_int 4 2 (by norm_num) (by norm_num) _ 980786 2
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 4 ∧ t = 3 := by omega
    exact of_cell (U := 883638 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 4 3 (by norm_num) (by norm_num) (883638 / 1000000)
        (by norm_num) (check_of_int 4 3 (by norm_num) (by norm_num) _ 883638 12
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 4 ∧ t = 4 := by omega
    exact of_cell (U := 604555 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 4 4 (by norm_num) (by norm_num) (604555 / 1000000)
        (by norm_num) (check_of_int 4 4 (by norm_num) (by norm_num) _ 604555 46
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 5 ∧ t = 2 := by omega
    exact of_cell (U := 995185 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 5 2 (by norm_num) (by norm_num) (995185 / 1000000)
        (by norm_num) (check_of_int 5 2 (by norm_num) (by norm_num) _ 995185 2
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 5 ∧ t = 3 := by omega
    exact of_cell (U := 970239 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 5 3 (by norm_num) (by norm_num) (970239 / 1000000)
        (by norm_num) (check_of_int 5 3 (by norm_num) (by norm_num) _ 970239 12
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 5 ∧ t = 4 := by omega
    exact of_cell (U := 867542 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 5 4 (by norm_num) (by norm_num) (867542 / 1000000)
        (by norm_num) (check_of_int 5 4 (by norm_num) (by norm_num) _ 867542 46
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 6 ∧ t = 2 := by omega
    exact of_cell (U := 998796 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 6 2 (by norm_num) (by norm_num) (998796 / 1000000)
        (by norm_num) (check_of_int 6 2 (by norm_num) (by norm_num) _ 998796 2
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 6 ∧ t = 3 := by omega
    exact of_cell (U := 992518 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 6 3 (by norm_num) (by norm_num) (992518 / 1000000)
        (by norm_num) (check_of_int 6 3 (by norm_num) (by norm_num) _ 992518 12
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 6 ∧ t = 4 := by omega
    exact of_cell (U := 965743 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 6 4 (by norm_num) (by norm_num) (965743 / 1000000)
        (by norm_num) (check_of_int 6 4 (by norm_num) (by norm_num) _ 965743 46
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 6 ∧ t = 5 := by omega
    exact of_cell (U := 864601 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 6 5 (by norm_num) (by norm_num) (864601 / 1000000)
        (by norm_num) (check_of_int 6 5 (by norm_num) (by norm_num) _ 864601 144
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 7 ∧ t = 6 := by omega
    exact of_cell (U := 868067 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 7 6 (by norm_num) (by norm_num) (868067 / 1000000)
        (by norm_num) (check_of_int 7 6 (by norm_num) (by norm_num) _ 868067 402
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ
  · obtain ⟨rfl, rfl⟩ : s = 8 ∧ t = 7 := by omega
    exact of_cell (U := 874299 / 1000000) rfl
      (fun _ hb _ hβ => norm_sum_le_of_check 8 7 (by norm_num) (by norm_num) (874299 / 1000000)
        (by norm_num) (check_of_int 8 7 (by norm_num) (by norm_num) _ 874299 1044
          (by norm_num) (by decide +kernel) (by decide +kernel)) hb hβ)
      hb hβ

end CollatzPosDens
