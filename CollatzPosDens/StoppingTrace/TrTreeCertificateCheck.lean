/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.StoppingTrace.TrCapCellBound
public import CollatzPosDens.StoppingTrace.TrTreeCost
public import CollatzPosDens.StoppingTrace.TrTreeCostNodeBound
public import CollatzPosDens.StoppingTrace.TrZeroDatum
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.IntervalCases

/-!
# The checker of the gap-zero certificate

Let `m` be an odd integer and `[a, b] ⊆ [-1/3, 1/3]` a cell with midpoint `u` and half-width
`δ`. For `β ∈ [a, b]` the tree cost `F^{cut⁰, W}_{0,0}(m + β)` of the gap-zero cutoff
`cut⁰ = CollatzPosDens.trZeroCutoff` and the white-test policy `W = W^{0,12,14}_{m,a,b}`
(`CollatzPosDens.trWhitePolicy`) is bounded from above by an explicit number computed with
integers only, and this file proves the bound sound.

The bound rests on the following facts.

* Writing `e(θ) = exp(2πiθ)`, the packet function is `Φ_t(θ) = t⁻¹ |∑_{j<t} e(2^j θ)|`, so
  the retained factor `Φ^cap_c(9^r X / 2^{h+c})` of the letter `c` at the node `(r, h)` is
  determined by the units `e(9^r X / 2^L)` with `h + 2 ≤ L ≤ h + c ≤ 17`. For each `r ≤ 7` these
  are the successive squares of `e(9^r X / 2^{17})`, which is computed from the Taylor
  polynomial of degree `17` of the exponential, after reducing the argument to `|τ| ≤ 1/8` and
  using `π` to twenty decimals.
* The capped factor `Φ^cap_c` has period `1`, and a bound `s` for the sum of units at the
  midpoint `X₀ = m + u` bounds it on the whole cell by
  `min {1, max {s/(c-1), 2^{-16}} + ℓ_c 9^r δ / 2^{h+c}}`
  (`CollatzPosDens.trCapFactor_le_min_of_norm_sum_le`).
* A factor whose argument has denominator `2^L` with `L ≤ k` depends only on `m` modulo `2^k`;
  factors not yet determined are bounded by `1`. Likewise a continuation `(r, h, c)` with
  `c ∈ {4, 5}` is used only when the white test of the policy is certified on the cell; the
  continuation value is at most `1` in any case.
* The tree cost is bounded node by node, from the deepest row of nodes `(r, ·)` up to the root,
  by the one-node bound `CollatzPosDens.trTreeCost_le_of_node_bound` with the factor bounds and
  the bounds already computed for the children.

## Main definitions

* `CollatzPosDens.TrTreeCertificate.facI`: the bound for a retained factor on a cell.
* `CollatzPosDens.TrTreeCertificate.edgeI`: the certified continuations of the policy.
* `CollatzPosDens.TrTreeCertificate.cellV`: the bound for the tree cost on a cell.

## Main results

* `CollatzPosDens.TrTreeCertificate.trTreeCost_le_rowsI`: the tree cost is bounded by the
  bound computed row by row.

## Implementation notes

All arithmetic of the checker is on integers, which the kernel evaluates with its built-in
big-number operations: units are `2^{-60}` for complex numbers and factors (`2^{-64}` for the
Taylor terms) and `2^{-72}` for tree costs, and every rounding is a floor or ceiling division
whose error is bounded by `abs_ediv_sub_le` or `div_le_ceil_ediv`, always in the safe direction.
The norm `|a + bi|` of a sum of units is bounded by the result `S` of three Newton steps for the
square root from above, and the checker verifies `a² + b² ≤ S²`; a failing check gives the bound
`1`.

The cost bounds of the nodes `(r, h)` are computed row by row (`rowsI`); each row is evaluated
completely (`forceRow`) before it is used, so that every node is evaluated once. A cover is a
tree: a residue class modulo `2^k` is either split into its two classes modulo `2^{k+1}`,
covered by a bisection tree of `[-1/3, 1/3]` in `β`, or empty in `(0, 2^16)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace TrTreeCertificate

open Complex Real

/-! ### The unit `e(θ)` -/

/-- The unit `e(θ) = exp(2πiθ)`. -/
noncomputable def ex (θ : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (θ : ℂ))

/-- `e(a + b) = e(a) e(b)`. -/
theorem ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  simp only [ex, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The unit `e(θ)` has norm `1`. -/
theorem norm_ex (θ : ℝ) : ‖ex θ‖ = 1 := by
  have : 2 * π * Complex.I * (θ : ℂ) = ((2 * π * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [ex, this, Complex.norm_exp_ofReal_mul_I]

/-- `e(n) = 1` for an integer `n`. -/
theorem ex_intCast (n : ℤ) : ex n = 1 := by
  have : 2 * π * Complex.I * (((n : ℝ)) : ℂ) = n * (2 * π * Complex.I) := by push_cast; ring
  rw [ex, this, Complex.exp_int_mul_two_pi_mul_I]

/-- The unit `e(θ)` has period `1`. -/
theorem ex_add_intCast (θ : ℝ) (n : ℤ) : ex (θ + n) = ex θ := by
  rw [ex_add, ex_intCast, mul_one]

/-- `e(m θ) = e(θ)^m` for a natural number `m`. -/
theorem ex_natCast_mul (m : ℕ) (θ : ℝ) : ex (m * θ) = ex θ ^ m := by
  induction m with
  | zero => simp [ex]
  | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, ex_add, ih, pow_succ]

/-- `e(1/4) = i`. -/
theorem ex_one_fourth : ex (1 / 4) = Complex.I := by
  conv_rhs => rw [← Complex.exp_pi_div_two_mul_I]
  rw [ex]
  congr 1
  push_cast
  ring

/-- `|exp(ia) - exp(ib)| ≤ |a - b|` for real `a` and `b`. -/
theorem norm_cexp_I_sub_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  have h : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
      Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- `e(θ) = exp(i · 2πθ)`. -/
theorem ex_eq_cexp (θ : ℝ) : ex θ = Complex.exp (Complex.I * ((2 * π * θ : ℝ) : ℂ)) := by
  rw [ex]
  congr 1
  push_cast
  ring

/-! ### Periodicity -/

/-- The capped packet factor has period `1`. -/
theorem trCapFactor_add_intCast (c : ℤ) (θ : ℝ) (n : ℤ) :
    trCapFactor c (θ + n) = trCapFactor c θ := by
  unfold trCapFactor
  rw [chPacketFn_add_intCast]

/-! ### Gaussian rationals -/

/-- The complex number `a + bi` of a pair of rationals. -/
noncomputable def toC (z : ℚ × ℚ) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

/-- The real part of `toC z` is `z.1`. -/
@[simp] theorem toC_re (z : ℚ × ℚ) : (toC z).re = z.1 := rfl

/-- The imaginary part of `toC z` is `z.2`. -/
@[simp] theorem toC_im (z : ℚ × ℚ) : (toC z).im = z.2 := rfl

/-! ### Taylor polynomials of `exp(iy)` -/

/-- The pair `(∑_{m<n} (iy)^m/m!, (iy)^n/n!)`, as pairs of rationals. -/
def expPolyAux (y : ℚ) : ℕ → (ℚ × ℚ) × (ℚ × ℚ)
  | 0 => ((0, 0), (1, 0))
  | n + 1 =>
    match expPolyAux y n with
    | ((s1, s2), (t1, t2)) => ((s1 + t1, s2 + t2), (-(t2 * y) / (n + 1), t1 * y / (n + 1)))

/-- `expPolyAux y n` is the pair `(∑_{m<n} (iy)^m/m!, (iy)^n/n!)`. -/
theorem expPolyAux_spec (y : ℚ) (n : ℕ) :
    toC (expPolyAux y n).1 =
        ∑ m ∈ Finset.range n, (Complex.I * (y : ℝ)) ^ m / (m.factorial : ℂ) ∧
      toC (expPolyAux y n).2 = (Complex.I * (y : ℝ)) ^ n / (n.factorial : ℂ) := by
  induction n with
  | zero => constructor <;> apply Complex.ext <;> simp [expPolyAux]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hs : (expPolyAux y (n + 1)).1 =
        ((expPolyAux y n).1.1 + (expPolyAux y n).2.1,
          (expPolyAux y n).1.2 + (expPolyAux y n).2.2) := rfl
    have ht : (expPolyAux y (n + 1)).2 =
        (-((expPolyAux y n).2.2 * y) / (n + 1), (expPolyAux y n).2.1 * y / (n + 1)) := rfl
    constructor
    · rw [hs, Finset.sum_range_succ, ← ih1, ← ih2]
      apply Complex.ext <;> simp
    · have h : (Complex.I * (y : ℝ)) ^ (n + 1) / ((n + 1).factorial : ℂ) =
          toC (expPolyAux y n).2 * (Complex.I * (y : ℝ)) / ((n : ℂ) + 1) := by
        rw [ih2, Nat.factorial_succ, pow_succ]
        push_cast
        have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        field_simp
      rw [h, ht]
      apply Complex.ext
      · simp only [toC_re, Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, toC_im, Complex.add_re,
          Complex.natCast_re, Complex.one_re, Complex.add_im, Complex.natCast_im,
          Complex.one_im, Complex.normSq_apply]
        push_cast
        field_simp
        ring
      · simp only [toC_im, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, toC_re, Complex.add_re,
          Complex.natCast_re, Complex.one_re, Complex.add_im, Complex.natCast_im,
          Complex.one_im, Complex.normSq_apply]
        push_cast
        field_simp
        ring

/-! ### Fixed-point arithmetic

The certificate computes with integers only. A number `a` stands for `a / 2^60`, and a pair
`(a, b)` for the complex number `(a + b i) / 2^60`. Every rounding is an integer floor
division `/` by a positive integer, and is accounted for by `abs_ediv_sub_le` or
`div_le_ceil_ediv`. -/

/-- The fixed-point unit `2^60`. -/
def P : ℤ := 1152921504606846976

/-- The fixed-point unit `P` is positive. -/
theorem P_pos : 0 < P := by norm_num [P]

/-- `P = 2^60`. -/
theorem cast_P : (P : ℝ) = 2 ^ 60 := by norm_num [P]

/-- The complex number `(a + b i) / 2^60` of a pair of integers. -/
noncomputable def toCI (z : ℤ × ℤ) : ℂ := ⟨z.1 / 2 ^ 60, z.2 / 2 ^ 60⟩

/-- The real part of `toCI z` is `z.1 / 2^60`. -/
@[simp] theorem toCI_re (z : ℤ × ℤ) : (toCI z).re = z.1 / 2 ^ 60 := rfl

/-- The imaginary part of `toCI z` is `z.2 / 2^60`. -/
@[simp] theorem toCI_im (z : ℤ × ℤ) : (toCI z).im = z.2 / 2 ^ 60 := rfl

/-- The integer floor division `m / D` is at most the real quotient `m / D`. -/
theorem ediv_le_div (m D : ℤ) (hD : 0 < D) : ((m / D : ℤ) : ℝ) ≤ m / D := by
  rw [le_div_iff₀ (by exact_mod_cast hD)]
  exact_mod_cast Int.ediv_mul_le m hD.ne'

/-- The real quotient `m / D` is less than the integer floor division `m / D` plus `1`. -/
theorem div_lt_ediv_add_one (m D : ℤ) (hD : 0 < D) : (m : ℝ) / D < (m / D : ℤ) + 1 := by
  rw [div_lt_iff₀ (by exact_mod_cast hD)]
  exact_mod_cast Int.lt_ediv_add_one_mul_self m hD

/-- The integer floor division `m / D` is within `1` of the real quotient `m / D`. -/
theorem abs_ediv_sub_le (m D : ℤ) (hD : 0 < D) : |((m / D : ℤ) : ℝ) - m / D| ≤ 1 := by
  have h1 := ediv_le_div m D hD
  have h2 := div_lt_ediv_add_one m D hD
  rw [abs_le]
  constructor <;> linarith

/-- `(x + D - 1) / D` is the ceiling of `x / D`. -/
theorem div_le_ceil_ediv (x D : ℤ) (hD : 0 < D) : (x : ℝ) / D ≤ (((x + D - 1) / D : ℤ) : ℝ) := by
  have h := Int.lt_ediv_add_one_mul_self (x + D - 1) hD
  rw [add_mul, one_mul] at h
  have h' : x ≤ (x + D - 1) / D * D := by linarith
  rw [div_le_iff₀ (by exact_mod_cast hD)]
  exact_mod_cast h'

/-- Rounding a pair down to a coarser mesh: `|⌊m / D⌋ / u - m / (D u)| ≤ 1 / u`. -/
theorem abs_ediv_div_sub_le (m D : ℤ) (hD : 0 < D) {u : ℝ} (hu : 0 < u) :
    |((m / D : ℤ) : ℝ) / u - m / (D * u)| ≤ 1 / u := by
  rw [← div_div, ← sub_div, abs_div, abs_of_pos hu]
  exact div_le_div_of_nonneg_right (abs_ediv_sub_le m D hD) hu.le

/-! ### The top of a chain: Taylor approximation of `e(q)` in fixed point -/

/-- The Taylor terms of `exp(iy)` at `y = Y / 2^60`, in fixed point with unit `2^64`: the pair
`(∑_{m<n} T_m, T_n)` with `T_0 = 1` and `T_{m+1} = ⌊T_m · iy / (m + 1)⌋`, rounded down in each
coordinate. -/
def expI (Y : ℤ) : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((0, 0), (18446744073709551616, 0))
  | n + 1 =>
    match expI Y n with
    | ((s1, s2), (t1, t2)) =>
      ((s1 + t1, s2 + t2), (-t2 * Y / (P * ((n : ℤ) + 1)), t1 * Y / (P * ((n : ℤ) + 1))))

/-- One rounded Taylor step loses at most one unit `2^{-64}`. -/
theorem abs_expI_step_le (T Y : ℤ) (b : ℝ) (n : ℕ) {e : ℝ} (hY : |(Y : ℝ) / 2 ^ 60| ≤ 1)
    (he : |(T : ℝ) / 2 ^ 64 - b| ≤ e) :
    |(((T * Y / (P * ((n : ℤ) + 1)) : ℤ) : ℝ)) / 2 ^ 64 - b * ((Y : ℝ) / 2 ^ 60) / (n + 1)| ≤
      e + 1 / 2 ^ 64 := by
  have hD : 0 < P * ((n : ℤ) + 1) := mul_pos P_pos (by positivity)
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h1 := abs_ediv_div_sub_le (T * Y) _ hD (by positivity : (0 : ℝ) < 2 ^ 64)
  have e1 : (((T * Y : ℤ) : ℝ)) / (((P * ((n : ℤ) + 1) : ℤ) : ℝ) * 2 ^ 64) =
      (T : ℝ) / 2 ^ 64 * ((Y : ℝ) / 2 ^ 60) / (n + 1) := by
    push_cast [cast_P]
    field_simp
  rw [e1] at h1
  have e2 : (((T * Y / (P * ((n : ℤ) + 1)) : ℤ) : ℝ)) / 2 ^ 64 - b * ((Y : ℝ) / 2 ^ 60) / (n + 1) =
      ((((T * Y / (P * ((n : ℤ) + 1)) : ℤ) : ℝ)) / 2 ^ 64 -
        (T : ℝ) / 2 ^ 64 * ((Y : ℝ) / 2 ^ 60) / (n + 1)) +
        ((T : ℝ) / 2 ^ 64 - b) * ((Y : ℝ) / 2 ^ 60) / (n + 1) := by ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  have he0 : 0 ≤ e := (abs_nonneg _).trans he
  have h2 : |((T : ℝ) / 2 ^ 64 - b) * ((Y : ℝ) / 2 ^ 60) / (n + 1)| ≤ e := by
    rw [abs_div, abs_mul, abs_of_pos hn, div_le_iff₀ hn]
    have h1n : (1 : ℝ) ≤ n + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc |(T : ℝ) / 2 ^ 64 - b| * |(Y : ℝ) / 2 ^ 60| ≤ e * 1 :=
          mul_le_mul he hY (abs_nonneg _) he0
      _ ≤ e * (n + 1) := by nlinarith
  linarith

/-- The fixed-point Taylor terms stay within `n · 2^{-64}` of the exact ones, and their sums
within `n^2 · 2^{-64}`, in each coordinate. -/
theorem abs_expI_sub_le (Y : ℤ) (hY : |(Y : ℝ) / 2 ^ 60| ≤ 1) (n : ℕ) :
    |((expI Y n).2.1 : ℝ) / 2 ^ 64 - ((expPolyAux ((Y : ℚ) / 2 ^ 60) n).2.1 : ℝ)| ≤
      (n : ℝ) / 2 ^ 64 ∧
    |((expI Y n).2.2 : ℝ) / 2 ^ 64 - ((expPolyAux ((Y : ℚ) / 2 ^ 60) n).2.2 : ℝ)| ≤
      (n : ℝ) / 2 ^ 64 ∧
    |((expI Y n).1.1 : ℝ) / 2 ^ 64 - ((expPolyAux ((Y : ℚ) / 2 ^ 60) n).1.1 : ℝ)| ≤
      (n : ℝ) ^ 2 / 2 ^ 64 ∧
    |((expI Y n).1.2 : ℝ) / 2 ^ 64 - ((expPolyAux ((Y : ℚ) / 2 ^ 60) n).1.2 : ℝ)| ≤
      (n : ℝ) ^ 2 / 2 ^ 64 := by
  induction n with
  | zero => norm_num [expI, expPolyAux]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    set A := expI Y n with hA
    set B := expPolyAux ((Y : ℚ) / 2 ^ 60) n with hB
    have eI : expI Y (n + 1) = ((A.1.1 + A.2.1, A.1.2 + A.2.2),
        (-A.2.2 * Y / (P * ((n : ℤ) + 1)), A.2.1 * Y / (P * ((n : ℤ) + 1)))) := rfl
    have eQ : expPolyAux ((Y : ℚ) / 2 ^ 60) (n + 1) = ((B.1.1 + B.2.1, B.1.2 + B.2.2),
        (-(B.2.2 * ((Y : ℚ) / 2 ^ 60)) / (n + 1), B.2.1 * ((Y : ℚ) / 2 ^ 60) / (n + 1))) := rfl
    rw [eI, eQ]
    dsimp only
    have hn1 : (n : ℝ) / 2 ^ 64 + 1 / 2 ^ 64 = ((n + 1 : ℕ) : ℝ) / 2 ^ 64 := by push_cast; ring
    have hn2 : (n : ℝ) ^ 2 / 2 ^ 64 + n / 2 ^ 64 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 / 2 ^ 64 := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      push_cast
      nlinarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h2' : |((-A.2.2 : ℤ) : ℝ) / 2 ^ 64 - -(B.2.2 : ℝ)| ≤ (n : ℝ) / 2 ^ 64 := by
        have e : ((-A.2.2 : ℤ) : ℝ) / 2 ^ 64 - -(B.2.2 : ℝ) = -((A.2.2 : ℝ) / 2 ^ 64 - B.2.2) := by
          push_cast
          ring
        rw [e, abs_neg]
        exact h2
      have c : (((-(B.2.2 * ((Y : ℚ) / 2 ^ 60)) / (n + 1) : ℚ)) : ℝ) =
          -(B.2.2 : ℝ) * ((Y : ℝ) / 2 ^ 60) / (n + 1) := by
        push_cast
        ring
      rw [c, ← hn1]
      exact abs_expI_step_le _ Y _ n hY h2'
    · have c : (((B.2.1 * ((Y : ℚ) / 2 ^ 60) / (n + 1) : ℚ)) : ℝ) =
          (B.2.1 : ℝ) * ((Y : ℝ) / 2 ^ 60) / (n + 1) := by
        push_cast
        ring
      rw [c, ← hn1]
      exact abs_expI_step_le _ Y _ n hY h1
    · have e : (((A.1.1 + A.2.1 : ℤ) : ℝ)) / 2 ^ 64 - ((B.1.1 + B.2.1 : ℚ) : ℝ) =
          ((A.1.1 : ℝ) / 2 ^ 64 - B.1.1) + ((A.2.1 : ℝ) / 2 ^ 64 - B.2.1) := by
        push_cast
        ring
      rw [e]
      exact (abs_add_le _ _).trans (by linarith)
    · have e : (((A.1.2 + A.2.2 : ℤ) : ℝ)) / 2 ^ 64 - ((B.1.2 + B.2.2 : ℚ) : ℝ) =
          ((A.1.2 : ℝ) / 2 ^ 64 - B.1.2) + ((A.2.2 : ℝ) / 2 ^ 64 - B.2.2) := by
        push_cast
        ring
      rw [e]
      exact (abs_add_le _ _).trans (by linarith)

/-- Multiplication by `i^n`. -/
def rotI : ℕ → ℤ × ℤ → ℤ × ℤ
  | 0, z => z
  | n + 1, z => rotI n (-z.2, z.1)

/-- `rotI n` is multiplication by `i^n`. -/
theorem toCI_rotI (n : ℕ) (z : ℤ × ℤ) : toCI (rotI n z) = Complex.I ^ n * toCI z := by
  induction n generalizing z with
  | zero => simp [rotI]
  | succ n ih =>
    rw [rotI, ih, pow_succ, mul_assoc]
    congr 1
    apply Complex.ext <;> simp [neg_div]

/-- The quarter-turn count `⌊4q + 1/2⌋` of `q = num / den`. -/
def topN (num : ℤ) (den : ℕ) : ℤ := (8 * num + den) / (2 * den)

/-- `⌊2^60 · 2 π₀ τ⌋` for the reduced argument `τ = q - topN / 4` of `q = num / den`, where
`π₀ = 314159265358979323846 / 10^20 < π`. -/
def topY (num : ℤ) (den : ℕ) : ℤ :=
  314159265358979323846 * P * (4 * num - topN num den * den) / (200000000000000000000 * den)

/-- An approximation of `e(num / den)`: reduce the argument to `τ` with `|τ| ≤ 1/8`, evaluate
the Taylor polynomial of degree `17` of `exp(iy)` in fixed point at a rounding `y` of `2π τ`,
round to the mesh `2^{-60}`, and rotate by `i^n`. -/
def topI (num : ℤ) (den : ℕ) : ℤ × ℤ :=
  match expI (topY num den) 18 with
  | ((a, b), _) => rotI (topN num den % 4).toNat (a / 16, b / 16)

/-- `topI num den` approximates `e(num / den)` within `116 · 2^{-60}`. -/
theorem norm_toCI_topI_sub_le (num : ℤ) {den : ℕ} (hden : 0 < den) :
    ‖toCI (topI num den) - ex (num / den)‖ ≤ 116 / 2 ^ 60 := by
  have hden' : (0 : ℝ) < den := by exact_mod_cast hden
  set q : ℝ := num / den with hq
  set n := topN num den with hn
  have h2den : (0 : ℤ) < 2 * den := by positivity
  have hn4 : (((8 * num + den : ℤ) : ℝ)) / ((2 * den : ℤ) : ℝ) = 4 * q + 1 / 2 := by
    rw [hq]
    push_cast
    field_simp
    ring
  have hn1 : (n : ℝ) ≤ 4 * q + 1 / 2 := hn4 ▸ ediv_le_div (8 * num + den) (2 * den) h2den
  have hn2 : 4 * q + 1 / 2 < n + 1 := hn4 ▸ div_lt_ediv_add_one (8 * num + den) (2 * den) h2den
  set τ : ℝ := q - n / 4 with hτ
  have hτ1 : -(1 / 8 : ℝ) ≤ τ := by rw [hτ]; linarith
  have hτ2 : τ ≤ 1 / 8 := by rw [hτ]; linarith
  set Y := topY num den with hY
  set p : ℝ := 314159265358979323846 / 10 ^ 20 with hp
  have hYr : |(Y : ℝ) / 2 ^ 60 - 2 * p * τ| ≤ 1 / 2 ^ 60 := by
    have h := abs_ediv_div_sub_le (314159265358979323846 * P * (4 * num - n * den))
      (200000000000000000000 * den) (by positivity) (by positivity : (0 : ℝ) < 2 ^ 60)
    have e : ((314159265358979323846 * P * (4 * num - n * den) : ℤ) : ℝ) /
        (((200000000000000000000 * den : ℤ) : ℝ) * 2 ^ 60) = 2 * p * τ := by
      rw [hτ, hq, hp]
      push_cast [cast_P]
      field_simp
      ring
    rw [e] at h
    exact h
  have hp1 : p ≤ 315 / 100 := by norm_num [hp]
  have hp0 : 0 ≤ p := by norm_num [hp]
  have hy1 : |(Y : ℝ) / 2 ^ 60| ≤ 4 / 5 := by
    rw [abs_le] at hYr ⊢
    constructor <;> nlinarith
  have hrot : ex q = Complex.I ^ (n % 4).toNat * ex τ := by
    have h4 : (0 : ℤ) ≤ n % 4 := Int.emod_nonneg n (by norm_num)
    have hq' : q = τ + ((((n % 4).toNat : ℕ) : ℝ) * (1 / 4) + ((n / 4 : ℤ) : ℝ)) := by
      have h1 : (((n % 4).toNat : ℕ) : ℤ) = n % 4 := Int.toNat_of_nonneg h4
      have h2 : (((n % 4).toNat : ℕ) : ℝ) = ((n % 4 : ℤ) : ℝ) := by exact_mod_cast h1
      rw [h2, hτ]
      have h3 : ((n % 4 : ℤ) : ℝ) = (n : ℝ) - 4 * ((n / 4 : ℤ) : ℝ) := by
        have := Int.emod_add_mul_ediv n 4
        have : ((n % 4 : ℤ) : ℝ) + 4 * ((n / 4 : ℤ) : ℝ) = n := by exact_mod_cast this
        linarith
      rw [h3]
      ring
    rw [hq', ex_add, ex_add, ex_intCast, mul_one, ex_natCast_mul, ex_one_fourth, mul_comm]
  have hpi1 : p < π := by
    have := Real.pi_gt_d20
    rw [hp]
    norm_num at this ⊢
    linarith
  have hpi2 : π < p + 1 / 10 ^ 20 := by
    have := Real.pi_lt_d20
    rw [hp]
    norm_num at this ⊢
    linarith
  have hE1 : ‖ex τ - Complex.exp (Complex.I * ((Y : ℝ) / 2 ^ 60 : ℝ))‖ ≤
      1 / 2 ^ 60 + 1 / 4 * (1 / 10 ^ 20) := by
    rw [ex_eq_cexp]
    refine (norm_cexp_I_sub_le _ _).trans ?_
    have e1 : 2 * π * τ - (Y : ℝ) / 2 ^ 60 = -((Y : ℝ) / 2 ^ 60 - 2 * p * τ) + 2 * (π - p) * τ := by
      ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < π - p)]
    have hτ' : |τ| ≤ 1 / 8 := abs_le.mpr ⟨hτ1, hτ2⟩
    have h5 : |(2 : ℝ)| * (π - p) * |τ| ≤ 2 * (1 / 10 ^ 20) * (1 / 8) := by
      rw [abs_two]
      apply mul_le_mul (by linarith) hτ' (abs_nonneg _) (by norm_num)
    linarith
  set E := expPolyAux ((Y : ℚ) / 2 ^ 60) 18 with hE
  have hyq : (((Y : ℚ) / 2 ^ 60 : ℚ) : ℝ) = (Y : ℝ) / 2 ^ 60 := by push_cast; ring
  have hE2 : ‖Complex.exp (Complex.I * ((Y : ℝ) / 2 ^ 60 : ℝ)) - toC E.1‖ ≤
      (4 / 5) ^ 18 * ((19 : ℝ) * ((Nat.factorial 18 : ℝ) * 18)⁻¹) := by
    rw [hE, (expPolyAux_spec _ 18).1, hyq]
    have hn' : ‖Complex.I * (((Y : ℝ) / 2 ^ 60 : ℝ) : ℂ)‖ = |(Y : ℝ) / 2 ^ 60| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have := Complex.exp_bound (x := Complex.I * (((Y : ℝ) / 2 ^ 60 : ℝ) : ℂ))
      (by rw [hn']; linarith) (n := 18) (by norm_num)
    refine this.trans ?_
    rw [hn']
    refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy1 18)
      (le_of_eq (by push_cast; norm_num)) (by positivity) (by positivity)
  set S := (expI Y 18).1 with hS
  have hE3 : ‖toC E.1 - ⟨(S.1 : ℝ) / 2 ^ 64, (S.2 : ℝ) / 2 ^ 64⟩‖ ≤ 2 * 18 ^ 2 / 2 ^ 64 := by
    obtain ⟨-, -, h3, h4⟩ := abs_expI_sub_le Y (hy1.trans (by norm_num)) 18
    rw [← hS, ← hE] at h3 h4
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, toC_re, toC_im]
    rw [abs_sub_comm, abs_sub_comm (E.1.2 : ℝ)]
    push_cast at h3 h4 ⊢
    linarith
  have hE4 : ‖(⟨(S.1 : ℝ) / 2 ^ 64, (S.2 : ℝ) / 2 ^ 64⟩ : ℂ) - toCI (S.1 / 16, S.2 / 16)‖ ≤
      2 / 2 ^ 60 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, toCI_re, toCI_im]
    have a1 := abs_ediv_div_sub_le S.1 16 (by norm_num) (by positivity : (0 : ℝ) < 2 ^ 60)
    have a2 := abs_ediv_div_sub_le S.2 16 (by norm_num) (by positivity : (0 : ℝ) < 2 ^ 60)
    rw [abs_sub_comm] at a1 a2
    norm_num at a1 a2 ⊢
    linarith
  have htop : topI num den = rotI (n % 4).toNat (S.1 / 16, S.2 / 16) := rfl
  rw [htop, toCI_rotI, hrot, ← mul_sub, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  have : toCI (S.1 / 16, S.2 / 16) - ex τ =
      -((ex τ - Complex.exp (Complex.I * ((Y : ℝ) / 2 ^ 60 : ℝ))) +
        (Complex.exp (Complex.I * ((Y : ℝ) / 2 ^ 60 : ℝ)) - toC E.1) +
        (toC E.1 - ⟨(S.1 : ℝ) / 2 ^ 64, (S.2 : ℝ) / 2 ^ 64⟩) +
        ((⟨(S.1 : ℝ) / 2 ^ 64, (S.2 : ℝ) / 2 ^ 64⟩ : ℂ) - toCI (S.1 / 16, S.2 / 16))) := by
    ring
  rw [this, norm_neg]
  refine (norm_add_le _ _).trans ?_
  have h3 := norm_add₃_le (a := ex τ - Complex.exp (Complex.I * ((Y : ℝ) / 2 ^ 60 : ℝ)))
    (b := Complex.exp (Complex.I * ((Y : ℝ) / 2 ^ 60 : ℝ)) - toC E.1)
    (c := toC E.1 - ⟨(S.1 : ℝ) / 2 ^ 64, (S.2 : ℝ) / 2 ^ 64⟩)
  have hf : (Nat.factorial 18 : ℝ) = 6402373705728000 := by norm_num [Nat.factorial]
  rw [hf] at hE2
  have hsum : 1 / 2 ^ 60 + 1 / 4 * (1 / 10 ^ 20) +
      (4 / 5) ^ 18 * ((19 : ℝ) * (6402373705728000 * 18)⁻¹) + 2 * 18 ^ 2 / 2 ^ 64 + 2 / 2 ^ 60 ≤
      116 / 2 ^ 60 := by norm_num
  linarith

/-! ### Chains of squares -/

/-- Rounded squaring of a fixed-point Gaussian integer. -/
def gsqI (z : ℤ × ℤ) : ℤ × ℤ := ((z.1 * z.1 - z.2 * z.2) / P, 2 * z.1 * z.2 / P)

/-- The error after one rounded squaring, in units `2^{-60}`, rounded up:
`e (2 + e) + 2 · 2^{-60}` for the error `e` of the input. -/
def errI (e : ℤ) : ℤ := (e * (2 * P + e) + P - 1) / P + 2

/-- If `z` approximates a unit `u` within `e · 2^{-60}`, then the rounded square `gsqI z`
approximates `u²` within `errI e · 2^{-60}`. -/
theorem norm_toCI_gsqI_sub_le {z : ℤ × ℤ} {u : ℂ} {e : ℤ} (hu : ‖u‖ = 1)
    (h : ‖toCI z - u‖ ≤ e / 2 ^ 60) : ‖toCI (gsqI z) - u ^ 2‖ ≤ errI e / 2 ^ 60 := by
  have he : (0 : ℝ) ≤ e / 2 ^ 60 := (norm_nonneg _).trans h
  have h1 : ‖toCI (gsqI z) - toCI z ^ 2‖ ≤ 2 / 2 ^ 60 := by
    have hsq : toCI z ^ 2 = ⟨((z.1 * z.1 - z.2 * z.2 : ℤ) : ℝ) / (P * 2 ^ 60),
        ((2 * z.1 * z.2 : ℤ) : ℝ) / (P * 2 ^ 60)⟩ := by
      apply Complex.ext <;> simp [sq, cast_P] <;> ring
    rw [hsq]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have a1 := abs_ediv_div_sub_le (z.1 * z.1 - z.2 * z.2) P P_pos
      (by positivity : (0 : ℝ) < 2 ^ 60)
    have a2 := abs_ediv_div_sub_le (2 * z.1 * z.2) P P_pos (by positivity : (0 : ℝ) < 2 ^ 60)
    simp only [Complex.sub_re, Complex.sub_im, toCI_re, toCI_im, gsqI]
    linarith
  have h2 : ‖toCI z ^ 2 - u ^ 2‖ ≤ e / 2 ^ 60 * (2 + e / 2 ^ 60) := by
    rw [sq_sub_sq, norm_mul]
    have : ‖toCI z + u‖ ≤ 2 + e / 2 ^ 60 := by
      have : toCI z + u = (toCI z - u) + 2 * u := by ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hu]
      norm_num
      linarith
    rw [mul_comm]
    exact mul_le_mul h this (norm_nonneg _) he
  have h3 : e / 2 ^ 60 * (2 + e / 2 ^ 60) + 2 / 2 ^ 60 ≤ (errI e : ℝ) / 2 ^ 60 := by
    have hc := div_le_ceil_ediv (e * (2 * P + e)) P P_pos
    have hE : (errI e : ℝ) = (((e * (2 * P + e) + P - 1) / P : ℤ) : ℝ) + 2 := by
      simp only [errI]
      push_cast
      ring
    rw [hE]
    have e1 : e / 2 ^ 60 * (2 + e / 2 ^ 60) + 2 / 2 ^ 60 =
        (((e * (2 * P + e) : ℤ) : ℝ) / P + 2) / (2 ^ 60 : ℝ) := by
      push_cast [cast_P]
      field_simp
    rw [e1]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have : toCI (gsqI z) - u ^ 2 = (toCI (gsqI z) - toCI z ^ 2) + (toCI z ^ 2 - u ^ 2) := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- The chain `[(z₀, e₀), …, (z_N, e_N)]` of successive rounded squares with their errors. -/
def chainI : ℕ → ℤ × ℤ → ℤ → List ((ℤ × ℤ) × ℤ)
  | 0, z, e => [(z, e)]
  | n + 1, z, e => (z, e) :: chainI n (gsqI z) (errI e)

/-- The `j`-th entry of the list approximates `e(2^j q)` within its recorded error. -/
def ChainGoodI (q : ℝ) (l : List ((ℤ × ℤ) × ℤ)) : Prop :=
  ∀ j (hj : j < l.length), ‖toCI l[j].1 - ex (2 ^ j * q)‖ ≤ l[j].2 / 2 ^ 60

/-- If `z` approximates `e(q)` within `e · 2^{-60}`, then the chain of rounded squares of `z`
approximates the units `e(2^j q)` within its recorded errors. -/
theorem chainGoodI_chainI (N : ℕ) {z : ℤ × ℤ} {e : ℤ} {q : ℝ} (h : ‖toCI z - ex q‖ ≤ e / 2 ^ 60) :
    ChainGoodI q (chainI N z e) := by
  induction N generalizing z e q with
  | zero =>
    intro j hj
    simp only [chainI, List.length_cons, List.length_nil] at hj
    obtain rfl : j = 0 := by omega
    simpa [chainI] using h
  | succ N ih =>
    intro j hj
    rcases j with _ | j
    · simpa [chainI] using h
    · have h2 : ‖toCI (gsqI z) - ex (2 * q)‖ ≤ errI e / 2 ^ 60 := by
        rw [show (2 : ℝ) * q = (2 : ℕ) * q by norm_num, ex_natCast_mul]
        exact norm_toCI_gsqI_sub_le (norm_ex q) h
      have := ih h2 j (by simpa [chainI] using hj)
      simp only [chainI, List.getElem_cons_succ]
      rwa [pow_succ, mul_assoc]

/-- Dropping the first `off` entries of a chain for `q` gives a chain for `2^off q`. -/
theorem ChainGoodI.drop {q : ℝ} {l : List ((ℤ × ℤ) × ℤ)} (h : ChainGoodI q l) (off : ℕ) :
    ChainGoodI (2 ^ off * q) (l.drop off) := by
  intro j hj
  rw [List.getElem_drop]
  have := h (off + j) (by simp at hj; omega)
  rwa [pow_add, mul_comm ((2 : ℝ) ^ off), mul_assoc] at this

/-- The sum of the first `n` entries of a chain, with the sum of their errors. Missing entries
are charged the error `1` each. -/
def sumI : ℕ → List ((ℤ × ℤ) × ℤ) → (ℤ × ℤ) × ℤ
  | 0, _ => ((0, 0), 0)
  | n + 1, [] => ((0, 0), ((n : ℤ) + 1) * P)
  | n + 1, (z, e) :: l =>
    match sumI n l with
    | ((a, b), f) => ((z.1 + a, z.2 + b), e + f)

/-- For a chain for `q`, `sumI n` approximates `∑_{j<n} e(2^j q)` within its accumulated
error. -/
theorem norm_sum_sub_sumI_le (n : ℕ) {q : ℝ} {l : List ((ℤ × ℤ) × ℤ)} (h : ChainGoodI q l) :
    ‖∑ j ∈ Finset.range n, ex (2 ^ j * q) - toCI (sumI n l).1‖ ≤ (sumI n l).2 / 2 ^ 60 := by
  induction n generalizing q l with
  | zero =>
    have : toCI (0, 0) = 0 := Complex.ext (by simp) (by simp)
    simp [sumI, this]
  | succ n ih =>
    rcases l with _ | ⟨⟨z, e⟩, l⟩
    · have : toCI (sumI (n + 1) []).1 = 0 := by apply Complex.ext <;> simp [sumI]
      rw [this, sub_zero]
      refine (norm_sum_le _ _).trans ?_
      simp [norm_ex, sumI, cast_P]
    · have h0 := h 0 (by simp)
      simp only [List.getElem_cons_zero, pow_zero, one_mul] at h0
      have h1 : ChainGoodI (2 * q) l := by
        intro j hj
        have := h (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rwa [pow_succ, mul_assoc] at this
      have ih' := ih h1
      have hs : sumI (n + 1) ((z, e) :: l) =
          ((z.1 + (sumI n l).1.1, z.2 + (sumI n l).1.2), e + (sumI n l).2) := rfl
      rw [hs, Finset.sum_range_succ']
      simp only [pow_zero, one_mul]
      have : toCI (z.1 + (sumI n l).1.1, z.2 + (sumI n l).1.2) = toCI z + toCI (sumI n l).1 := by
        apply Complex.ext <;> simp [add_div]
      rw [this]
      have e1 : ∑ j ∈ Finset.range n, ex (2 ^ (j + 1) * q) + ex q - (toCI z + toCI (sumI n l).1)
          = (∑ j ∈ Finset.range n, ex (2 ^ j * (2 * q)) - toCI (sumI n l).1) - (toCI z - ex q) := by
        rw [Finset.sum_congr rfl fun j _ => by rw [pow_succ, mul_assoc]]
        ring
      rw [e1]
      refine (norm_sub_le _ _).trans ?_
      push_cast
      rw [add_div]
      linarith

/-! ### Square roots -/

/-- A first approximation `max |a| |b| + ⌊min |a| |b| / 2⌋ + 1` of `√(a² + b²)`. -/
def sqGuess (a b : ℤ) : ℕ := max a.natAbs b.natAbs + min a.natAbs b.natAbs / 2 + 1

/-- `n` steps of Newton's iteration `q ↦ ⌈(N + q²) / (2q)⌉` for `√N`, from `q`. -/
def newtonUp (N : ℕ) : ℕ → ℕ → ℕ
  | 0, q => q
  | n + 1, q => newtonUp N n ((N + q * q + 2 * q - 1) / (2 * q))

/-- If `a² + b² ≤ S²` then `|(a + bi) / 2^60| ≤ S / 2^60`. -/
theorem norm_toCI_le {a b : ℤ} {S : ℕ} (h : (a * a + b * b).toNat ≤ S * S) :
    ‖toCI (a, b)‖ ≤ S / 2 ^ 60 := by
  have h0 : 0 ≤ a * a + b * b := by nlinarith
  have h1 : a * a + b * b ≤ (S : ℤ) * S := by
    have e := Int.toNat_of_nonneg h0
    have h' : (((a * a + b * b).toNat : ℕ) : ℤ) ≤ ((S * S : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), Complex.sq_norm, Complex.normSq_apply]
  simp only [toCI_re, toCI_im]
  have h2 : ((a * a + b * b : ℤ) : ℝ) ≤ (((S : ℤ) * S : ℤ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  have e1 : (a : ℝ) / 2 ^ 60 * ((a : ℝ) / 2 ^ 60) + (b : ℝ) / 2 ^ 60 * ((b : ℝ) / 2 ^ 60) =
      ((a : ℝ) * a + b * b) / 2 ^ 120 := by ring
  have e2 : ((S : ℝ) / 2 ^ 60) ^ 2 = (S : ℝ) * S / 2 ^ 120 := by ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right h2 (by positivity)

/-! ### Upper bounds for the capped factors -/

/-- The numerator `lnum c = 7 (c - 1) ℓ_c` of the Lipschitz constant `ℓ_c` of the capped
factor, for `3 ≤ c ≤ 12`. -/
def lnum : ℕ → ℤ
  | 3 => 44 | 4 => 132 | 5 => 396 | 6 => 924 | 7 => 2156 | 8 => 4620 | 9 => 9900
  | 10 => 20460 | 11 => 42284 | 12 => 85932 | _ => 0

/-- `ℓ_c = lnum c / (7 (c - 1))` for `3 ≤ c ≤ 12`. -/
theorem trLipConst_eq_lnum {c : ℕ} (h3 : 3 ≤ c) (h12 : c ≤ 12) :
    (trLipConst c : ℝ) = lnum c / (7 * ((c : ℝ) - 1)) := by
  have : trLipConst c = lnum c / (7 * ((c : ℚ) - 1)) := by
    interval_cases c <;> simp [trLipConst, lnum, Finset.sum_range_succ] <;> norm_num
  rw [this]
  push_cast
  ring

/-- The bound, in units `2^{-60}`, for a capped factor `Φ^cap_{t+1}` from the sum `T` of `t`
chain entries with its error, and a Lipschitz term `lip`: with `S` an upper bound for the
norm of the sum, `min (max ⌈(S + E) / t⌉ 2^{44} + lip) 2^{60}`, and `2^{60}` (the bound `1`) if the
bound `S` fails. -/
def capI (t : ℕ) (T : (ℤ × ℤ) × ℤ) (lip : ℤ) : ℤ :=
  if (T.1.1 * T.1.1 + T.1.2 * T.1.2).toNat ≤
      newtonUp (T.1.1 * T.1.1 + T.1.2 * T.1.2).toNat 3 (sqGuess T.1.1 T.1.2) *
        newtonUp (T.1.1 * T.1.1 + T.1.2 * T.1.2).toNat 3 (sqGuess T.1.1 T.1.2) then
    min (max (((newtonUp (T.1.1 * T.1.1 + T.1.2 * T.1.2).toNat 3 (sqGuess T.1.1 T.1.2) : ℤ) +
      T.2 + t - 1) / t) 17592186044416 + lip) P
  else P

/-- For a chain for `θ₀` and a Lipschitz term `lip` bounding `ℓ_c |θ - θ₀|`, the capped factor
`Φ^cap_c(θ)` is at most `capI (c - 1) (sumI (c - 1) l) lip · 2^{-60}`. -/
theorem trCapFactor_le_capI {c : ℕ} (h3 : 3 ≤ c) (h16 : c ≤ 16) {l : List ((ℤ × ℤ) × ℤ)}
    {θ₀ : ℝ} (hl : ChainGoodI θ₀ l) {θ : ℝ} {lip : ℤ}
    (hlip : (trLipConst c : ℝ) * |θ - θ₀| ≤ lip / 2 ^ 60) :
    trCapFactor c θ ≤ capI (c - 1) (sumI (c - 1) l) lip / 2 ^ 60 := by
  set t := c - 1 with ht
  have ht1 : 1 ≤ t := by omega
  have htR : (0 : ℝ) < t := by exact_mod_cast ht1
  set T := sumI t l with hT
  set N := (T.1.1 * T.1.1 + T.1.2 * T.1.2).toNat with hN
  set S := newtonUp N 3 (sqGuess T.1.1 T.1.2) with hS
  have hcap : capI t T lip = if N ≤ S * S then
      min (max (((S : ℤ) + T.2 + t - 1) / t) 17592186044416 + lip) P else P := rfl
  rw [hcap]
  split_ifs with hw
  · have hsum := norm_sum_sub_sumI_le t hl
    rw [← hT] at hsum
    have hnorm : ‖toCI T.1‖ ≤ S / 2 ^ 60 := norm_toCI_le hw
    have hs : ‖∑ j ∈ Finset.range ((c : ℤ).toNat - 1),
        Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ j * θ₀ : ℝ) : ℂ))‖ ≤
        ((S : ℝ) + T.2) / 2 ^ 60 := by
      rw [Int.toNat_natCast, ← ht]
      have := norm_le_insert' (∑ j ∈ Finset.range t, ex (2 ^ j * θ₀)) (toCI T.1)
      change ‖∑ j ∈ Finset.range t, ex (2 ^ j * θ₀)‖ ≤ _
      rw [add_div]
      linarith
    have hb := trCapFactor_le_min_of_norm_sum_le (c := (c : ℤ)) (by exact_mod_cast h3)
      (by exact_mod_cast h16) θ θ₀ _ hs
    have hcR : ((c : ℤ) : ℝ) - 1 = t := by
      rw [ht, Nat.cast_sub (by omega : 1 ≤ c)]
      push_cast
      ring
    have hceil := div_le_ceil_ediv ((S : ℤ) + T.2) t (by exact_mod_cast ht1)
    refine hb.trans ?_
    rw [Int.cast_min, ← min_div_div_right (by positivity), cast_P, div_self (by positivity)]
    refine le_min ((min_le_right _ _).trans ?_) (min_le_left _ _)
    have h1 : ((S : ℝ) + T.2) / 2 ^ 60 / (((c : ℤ) : ℝ) - 1) ≤
        ((((S : ℤ) + T.2 + t - 1) / t : ℤ) : ℝ) / 2 ^ 60 := by
      rw [hcR, div_div, mul_comm, ← div_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      push_cast at hceil ⊢
      exact hceil
    have hmax := max_le_max h1
      (le_of_eq (show (2 : ℝ) ^ (-16 : ℤ) = ((17592186044416 : ℤ) : ℝ) / 2 ^ 60 by norm_num))
    rw [max_div_div_right (by positivity)] at hmax
    refine (add_le_add hmax hlip).trans (le_of_eq ?_)
    push_cast
    ring
  · rw [cast_P, div_self (by positivity)]
    exact trCapFactor_le_one _ _

/-- The argument `s x / 2^L` at `x = (r + 2^k n) + β` agrees modulo `1` with a point within
`s / (3 · 2^{d+L})` of `2^{Ltop - L} q`, where `q = s (3 · 2^d r + m) / (3 · 2^{d + Ltop})`, when
`L ≤ k`, `L ≤ Ltop` and `|β - m / (3 · 2^d)| ≤ 1 / (3 · 2^d)`. -/
theorem exists_argI (k L Ltop d s : ℕ) (r n m : ℤ) (β : ℝ)
    (hβ : |β - m / (3 * 2 ^ d)| ≤ 1 / (3 * 2 ^ d)) (hk : L ≤ k) (hL : L ≤ Ltop) :
    ∃ (θ' : ℝ) (j : ℤ), (s : ℝ) * (((r + 2 ^ k * n : ℤ) : ℝ) + β) / 2 ^ L = θ' + j ∧
      |θ' - 2 ^ (Ltop - L) * (((s * (3 * (2 ^ d : ℕ) * r + m) : ℤ) : ℝ) /
        ((3 * 2 ^ (d + Ltop) : ℕ) : ℝ))| ≤ ((s : ℤ) : ℝ) / (3 * 2 ^ (d + L)) := by
  refine ⟨(s : ℝ) * (r + β) / 2 ^ L, s * 2 ^ (k - L) * n, ?_, ?_⟩
  · have : (2 : ℝ) ^ k = 2 ^ (k - L) * 2 ^ L := by rw [← pow_add, Nat.sub_add_cancel hk]
    push_cast
    rw [this]
    field_simp
    ring
  · have h1 : (2 : ℝ) ^ Ltop = 2 ^ (Ltop - L) * 2 ^ L := by
      rw [← pow_add, Nat.sub_add_cancel hL]
    have e : (s : ℝ) * (r + β) / 2 ^ L -
        2 ^ (Ltop - L) * (((s * (3 * (2 ^ d : ℕ) * r + m) : ℤ) : ℝ) /
          ((3 * 2 ^ (d + Ltop) : ℕ) : ℝ)) = s / 2 ^ L * (β - m / (3 * 2 ^ d)) := by
      push_cast
      rw [pow_add, h1]
      field_simp
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    calc (s : ℝ) / 2 ^ L * |β - m / (3 * 2 ^ d)| ≤ s / 2 ^ L * (1 / (3 * 2 ^ d)) :=
          mul_le_mul_of_nonneg_left hβ (by positivity)
      _ = ((s : ℤ) : ℝ) / (3 * 2 ^ (d + L)) := by push_cast; rw [pow_add]; field_simp

/-- The chains of the cell with numerator `x`: for `r < 8`, the chain of successive squares
starting from an approximation of `e(9^r x / (3 · 2^{d+17}))`. -/
def chainsI (x : ℤ) (d : ℕ) : List (List ((ℤ × ℤ) × ℤ)) :=
  (List.range 8).map fun r => chainI 15 (topI (((9 ^ r : ℕ) : ℤ) * x) (3 * 2 ^ (d + 17))) 116

/-- The Lipschitz term `⌈ℓ_c 9^r 2^{60} / (3 · 2^{d+L})⌉`, in units `2^{-60}`. -/
def lipI (d r L c : ℕ) : ℤ :=
  (lnum c * ((9 ^ r : ℕ) : ℤ) * P + 21 * ((c : ℤ) - 1) * ((2 ^ (d + L) : ℕ) : ℤ) - 1) /
    (21 * ((c : ℤ) - 1) * ((2 ^ (d + L) : ℕ) : ℤ))

/-- The bound, in units `2^{-60}`, for the retained factor of the letter `c` at the node
`(r, h)`: `2^{60}` (the bound `1`) unless `3 ≤ c ≤ 12`, `r < 8` and `L = h + c ≤ min k 17`
(the argument is determined by the residue class modulo `2^k`). -/
def facI (k d r h c : ℕ) (chs : List (List ((ℤ × ℤ) × ℤ))) : ℤ :=
  if 3 ≤ c ∧ c ≤ 12 ∧ r < 8 ∧ h + c ≤ k ∧ h + c ≤ 17 then
    capI (c - 1) (sumI (c - 1) ((chs.getD r []).drop (17 - (h + c)))) (lipI d r (h + c) c)
  else P

/-- `2^{(a : ℤ) + (b : ℤ)} = 2^{a + b}` for natural numbers `a` and `b`. -/
theorem two_zpow_add (a b : ℕ) : (2 : ℝ) ^ ((a : ℤ) + (b : ℤ)) = 2 ^ (a + b) := by
  rw [← Nat.cast_add, zpow_natCast]

/-- On the cell `|β - p / (3 · 2^d)| ≤ 1 / (3 · 2^d)`, the retained factor of the letter `c` at
the node `(r, h)` at `res + 2^k n + β` is at most `facI · 2^{-60}`. -/
theorem trTreeFactor_le_facI {k d r h c : ℕ} (hc : c ≤ trZeroCutoff h) (hc2 : 2 ≤ c)
    {res n p : ℤ} {β : ℝ} (hβ : |β - p / (3 * 2 ^ d)| ≤ 1 / (3 * 2 ^ d)) :
    trTreeFactor trZeroCutoff r h c (((res + 2 ^ k * n : ℤ) : ℝ) + β) ≤
      facI k d r h c (chainsI (3 * (2 ^ d : ℕ) * res + p) d) / 2 ^ 60 := by
  rw [trTreeFactor_of_mem (by exact_mod_cast hc2) (by exact_mod_cast hc), two_zpow_add]
  unfold facI
  split_ifs with hg
  · obtain ⟨h3, h12, hr, hk, h17⟩ := hg
    have hch : (chainsI (3 * (2 ^ d : ℕ) * res + p) d).getD r [] =
        chainI 15 (topI (((9 ^ r : ℕ) : ℤ) * (3 * (2 ^ d : ℕ) * res + p)) (3 * 2 ^ (d + 17)))
          116 := by
      simp [chainsI, List.getD_eq_getElem?_getD, hr]
    rw [hch]
    have hgood := chainGoodI_chainI 15 (q := (((9 ^ r : ℕ) : ℤ) *
      (3 * (2 ^ d : ℕ) * res + p) : ℤ) / ((3 * 2 ^ (d + 17) : ℕ) : ℝ))
      (norm_toCI_topI_sub_le _ (by positivity))
    obtain ⟨θ', j, hθ, hθ'⟩ := exists_argI k (h + c) 17 d (9 ^ r) res n p β hβ hk h17
    have e9 : ((9 : ℝ) ^ r) = ((9 ^ r : ℕ) : ℝ) := by push_cast; rfl
    rw [e9, hθ, trCapFactor_add_intCast]
    refine trCapFactor_le_capI h3 (by omega) (hgood.drop _) ?_
    rw [trLipConst_eq_lnum h3 h12]
    have hc1 : (0 : ℝ) < (c : ℝ) - 1 := by
      have : (3 : ℝ) ≤ c := by exact_mod_cast h3
      linarith
    have hD : (0 : ℤ) < 21 * ((c : ℤ) - 1) * ((2 ^ (d + (h + c)) : ℕ) : ℤ) := by
      have : (3 : ℤ) ≤ c := by exact_mod_cast h3
      have : (0 : ℤ) < ((2 ^ (d + (h + c)) : ℕ) : ℤ) := by positivity
      nlinarith
    have hceil := div_le_ceil_ediv (lnum c * ((9 ^ r : ℕ) : ℤ) * P) _ hD
    have hl0 : (0 : ℝ) ≤ lnum c / (7 * ((c : ℝ) - 1)) := by
      rw [← trLipConst_eq_lnum h3 h12]
      exact_mod_cast trLipConst_nonneg c
    calc (lnum c : ℝ) / (7 * ((c : ℝ) - 1)) *
          |θ' - 2 ^ (17 - (h + c)) * ((((9 ^ r : ℕ) : ℤ) * (3 * (2 ^ d : ℕ) * res + p) : ℤ) /
            ((3 * 2 ^ (d + 17) : ℕ) : ℝ))|
        ≤ (lnum c : ℝ) / (7 * ((c : ℝ) - 1)) * ((((9 ^ r : ℕ) : ℤ) : ℝ) /
            (3 * 2 ^ (d + (h + c)))) := mul_le_mul_of_nonneg_left hθ' hl0
      _ = ((lnum c * ((9 ^ r : ℕ) : ℤ) * P : ℤ) : ℝ) /
            ((21 * ((c : ℤ) - 1) * ((2 ^ (d + (h + c)) : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ 60 := by
          push_cast [cast_P]
          field_simp
          ring
      _ ≤ (lipI d r (h + c) c : ℝ) / 2 ^ 60 :=
          div_le_div_of_nonneg_right hceil (by positivity)
  · rw [cast_P, div_self (by positivity)]
    exact trCapFactor_le_one _ _

/-! ### The white test -/

/-- The certified white test at the continuation `(r, h, c)`, `L = h + c`, of the cell with
numerator `x`: `L ≤ k` and `ε_* < dist(9^r x / D, ℤ) - 9^r / D` with `D = 3 · 2^{d+L}`, checked
as `37037 D < 10^6 (min (N % D) (D - N % D) - 9^r)` for `N = 9^r x`. -/
def whiteI (k d r L : ℕ) (x : ℤ) : Bool :=
  decide (L ≤ k) && decide (37037 * ((3 * 2 ^ (d + L) : ℕ) : ℤ) < 1000000 *
    (min ((((9 ^ r : ℕ) : ℤ) * x) % ((3 * 2 ^ (d + L) : ℕ) : ℤ))
      (((3 * 2 ^ (d + L) : ℕ) : ℤ) - (((9 ^ r : ℕ) : ℤ) * x) % ((3 * 2 ^ (d + L) : ℕ) : ℤ)) -
      ((9 ^ r : ℕ) : ℤ)))

/-- The certified continuations: `2 ≤ c ≤ 12`, `h + c ≤ 14`, and `c ∉ {4, 5}` or the white
test passes. -/
def edgeI (k d r h c : ℕ) (x : ℤ) : Bool :=
  decide (2 ≤ c) && decide (c ≤ 12) && decide (h + c ≤ 14) &&
    (!(c == 4 || c == 5) || whiteI k d r (h + c) x)

/-- A certified continuation `(r, h, c)` belongs to the white-test policy
`W^{0,12,14}_{res + 2^k n, a, b}` of the cell
`[a, b] = [(p - 1) / (3 · 2^d), (p + 1) / (3 · 2^d)]`. -/
theorem mem_trWhitePolicy_of_edgeI {k d r h c : ℕ} {res n p : ℤ}
    (he : edgeI k d r h c (3 * (2 ^ d : ℕ) * res + p) = true) :
    (r, h, c) ∈ trWhitePolicy 0 12 14 (res + 2 ^ k * n) ((p - 1) / (3 * 2 ^ d))
      ((p + 1) / (3 * 2 ^ d)) := by
  simp only [edgeI, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at he
  obtain ⟨⟨⟨h2, h12⟩, h14⟩, hw⟩ := he
  refine mem_trWhitePolicy.mpr ⟨h2, by exact_mod_cast h12, by exact_mod_cast h14, ?_⟩
  by_cases h45 : c = 4 ∨ c = 5
  · refine Or.inr (Or.inr ?_)
    have hw' : whiteI k d r (h + c) (3 * (2 ^ d : ℕ) * res + p) = true := by
      rcases hw with hw | hw
      · simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hw
        omega
      · exact hw
    simp only [whiteI, Bool.and_eq_true, decide_eq_true_eq] at hw'
    obtain ⟨hk, hw⟩ := hw'
    set L := h + c with hL
    set x : ℤ := 3 * (2 ^ d : ℕ) * res + p with hx
    set D : ℕ := 3 * 2 ^ (d + L) with hD
    set N : ℤ := ((9 ^ r : ℕ) : ℤ) * x with hN
    set ρ : ℤ := N % (D : ℤ) with hρ
    have hD0 : (0 : ℝ) < D := by positivity
    have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ (by positivity)
    have hρD : ρ < D := Int.emod_lt_of_pos _ (by positivity)
    have hy : (9 : ℝ) ^ r * (2 ^ 0 * (((res + 2 ^ k * n : ℤ)) : ℝ) +
        ((p - 1) / (3 * 2 ^ d) + (p + 1) / (3 * 2 ^ d)) / 2) / 2 ^ L =
        (N : ℝ) / (D : ℝ) + (((9 ^ r : ℕ) : ℤ) * 2 ^ (k - L) * n : ℤ) := by
      have : (2 : ℝ) ^ k = 2 ^ (k - L) * 2 ^ L := by rw [← pow_add, Nat.sub_add_cancel hk]
      rw [hN, hx, hD]
      push_cast
      rw [this, pow_add]
      field_simp
      ring
    have hwidth : (9 : ℝ) ^ r * ((p + 1) / (3 * 2 ^ d) - (p - 1) / (3 * 2 ^ d)) / 2 ^ (L + 1) =
        ((9 ^ r : ℕ) : ℝ) / D := by
      rw [hD]
      push_cast
      rw [pow_add, pow_succ]
      field_simp
      ring
    rw [hy, hwidth, round_add_intCast, Int.cast_add, add_sub_add_right_eq_sub, abs_sub_round_eq_min,
      Int.fract_div_intCast_eq_div_intCast_mod, ← hρ, one_sub_div hD0.ne',
      min_div_div_right hD0.le, epsStar_cast, ← sub_div, lt_div_iff₀ hD0]
    have hw' : ((37037 * (D : ℤ) : ℤ) : ℝ) < ((1000000 * (min ρ ((D : ℤ) - ρ) -
        ((9 ^ r : ℕ) : ℤ)) : ℤ) : ℝ) := by exact_mod_cast hw
    push_cast at hw' ⊢
    have : ((min ρ ((D : ℤ) - ρ) : ℤ) : ℝ) = min (ρ : ℝ) ((D : ℝ) - ρ) := by push_cast; rfl
    linarith
  · exact Or.inl fun hc => h45 (by simpa using hc)

/-! ### The tree bound -/

/-- The fixed-point unit `2^72` of the tree costs. -/
def Q : ℤ := 4722366482869645213696

/-- `Q = 2^72`. -/
theorem cast_Q : (Q : ℝ) = 2 ^ 72 := by norm_num [Q]

/-- The Pascal weight `ϖ(c) = (c - 1) 2^{-c}`, in units `2^{-12}`, for `c ≤ 12`. -/
def wq (c : ℕ) : ℤ := ((c : ℤ) - 1) * ((2 ^ (12 - c) : ℕ) : ℤ)

/-- `ϖ(c) = wq c · 2^{-12}` for `2 ≤ c ≤ 12`. -/
theorem varpi_eq_wq {c : ℕ} (h2 : 2 ≤ c) (h12 : c ≤ 12) :
    varpi (c : ℤ) = (wq c : ℝ) / 2 ^ 12 := by
  rw [varpi_of_two_le (by exact_mod_cast h2), wq, zpow_neg, zpow_natCast]
  have : (2 : ℝ) ^ 12 = 2 ^ (12 - c) * 2 ^ c := by rw [← pow_add, Nat.sub_add_cancel h12]
  rw [this]
  push_cast
  field_simp

/-- The product of `f` (units `2^{-60}`) and `g` (units `2^{-72}`), rounded up to units
`2^{-60}`. -/
def mulUp (f g : ℤ) : ℤ := (f * g + Q - 1) / Q

/-- `mulUp f g` bounds the product `(f · 2^{-60}) (g · 2^{-72})` from above. -/
theorem le_mulUp (f g : ℤ) :
    (f : ℝ) / 2 ^ 60 * ((g : ℝ) / 2 ^ 72) ≤ (mulUp f g : ℝ) / 2 ^ 60 := by
  have h := div_le_ceil_ediv (f * g) Q (by norm_num [Q])
  have e : (f : ℝ) / 2 ^ 60 * ((g : ℝ) / 2 ^ 72) = ((f * g : ℤ) : ℝ) / (Q : ℝ) / 2 ^ 60 := by
    rw [cast_Q]
    push_cast
    ring
  rw [e]
  exact div_le_div_of_nonneg_right h (by positivity)

/-- The cost bound, in units `2^{-72}`, at the node `(r, h)`, given the bounds `next` of the
nodes `(r + 1, ·)`: `2^{72} - ∑_{c=2}^{cut⁰(h)} ϖ(c) (2^{72} - ψ⁺_c G⁺_c)`, where `ψ⁺_c` is the
factor bound and `G⁺_c` is `next[h + c]` for a certified continuation and `2^{72}` otherwise. -/
def stateI (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (next : List ℤ) (r h : ℕ) : ℤ :=
  Q - ((List.range' 2 (trZeroCutoff h - 1)).map fun c : ℕ =>
    wq c * (P - mulUp (facI k d r h c chs)
      (if edgeI k d r h c x then next.getD (h + c) Q else Q))).sum

/-- The nodes `(r, h)` reached from the root through continuations with `2 ≤ c` and
`h + c ≤ 14`. -/
def live (r h : ℕ) : Bool :=
  (r == 0 && h == 0) || (decide (1 ≤ r) && decide (2 * r ≤ h) && decide (h ≤ 14))

/-- The cost bounds of the nodes `(r, h)`, `h < 18`, given those of the nodes `(r + 1, ·)`;
nodes that are not reached carry the bound `2^{72}`. -/
def rowI (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) (next : List ℤ) (r : ℕ) :
    List ℤ :=
  (List.range 18).map fun h => if live r h then stateI k d x chs next r h else Q

/-- Evaluate every entry of a list of integers before passing it on. -/
def forceRow {β : Type} : List ℤ → (List ℤ → β) → β
  | [], f => f []
  | v :: l, f => match v with
    | .ofNat n => forceRow l (fun l' => f (.ofNat n :: l'))
    | .negSucc n => forceRow l (fun l' => f (.negSucc n :: l'))

/-- `forceRow l f = f l`. -/
theorem forceRow_eq {β : Type} (l : List ℤ) (f : List ℤ → β) : forceRow l f = f l := by
  induction l generalizing f with
  | nil => rfl
  | cons v l ih => cases v <;> simp [forceRow, ih]

/-- The cost bound at the root, from the bounds `next` of the nodes `(n, ·)`, computing the
rows `n - 1, …, 0` in turn. -/
def rowsI (k d : ℕ) (x : ℤ) (chs : List (List ((ℤ × ℤ) × ℤ))) : ℕ → List ℤ → ℤ
  | 0, next => next.getD 0 Q
  | n + 1, next => forceRow (rowI k d x chs next n) (rowsI k d x chs n)

/-- A row of cost bounds for the nodes `(r, ·)`. -/
def RowBound (W : Set (ℕ × ℕ × ℕ)) (X : ℝ) (r : ℕ) (row : List ℤ) : Prop :=
  ∀ h, trTreeCost trZeroCutoff W r h X ≤ (row.getD h Q : ℝ) / 2 ^ 72

/-- A sum over `Finset.Icc 2 n` as the sum of a list over `List.range' 2 (n - 1)`. -/
theorem sum_Icc_eq_range' (n : ℕ) (F : ℕ → ℝ) :
    ∑ c ∈ Finset.Icc 2 n, F c = ((List.range' 2 (n - 1)).map F).sum := by
  rw [Nat.Icc_eq_range', show n + 1 - 2 = n - 1 by omega]
  change ((List.range' 2 (n - 1) : Multiset ℕ).map F).sum = _
  rw [Multiset.map_coe, Multiset.sum_coe]

section Bound

variable {W : Set (ℕ × ℕ × ℕ)} {X : ℝ} {k d : ℕ} {x : ℤ} {chs : List (List ((ℤ × ℤ) × ℤ))}

/-- The constant row `2^{72}`, the bound `1`, is a row of cost bounds. -/
theorem rowBound_replicate (r : ℕ) : RowBound W X r (List.replicate 18 Q) := by
  intro h
  have : ((List.replicate 18 Q).getD h Q : ℝ) = 2 ^ 72 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> simp [cast_Q]
  rw [this, div_self (by positivity)]
  exact trTreeCost_le_one _ _ _ _ _

/-- The real cast of a list sum, divided by `2^72`, is the sum of the divided casts. -/
theorem cast_sum_map_div (l : List ℕ) (T : ℕ → ℤ) :
    (((l.map T).sum : ℤ) : ℝ) / 2 ^ 72 = (l.map fun c => (T c : ℝ) / 2 ^ 72).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp only [List.map_cons, List.sum_cons, Int.cast_add, add_div, ih]

/-- Given factor bounds `facI`, certified continuations in `W` and a row of cost bounds for the
nodes `(r + 1, ·)`, the tree cost at the node `(r, h)` is at most `stateI · 2^{-72}`. -/
theorem trTreeCost_le_stateI (hW : IsBoundedPolicy W)
    (hfac : ∀ r h c, 2 ≤ c → c ≤ trZeroCutoff h →
      trTreeFactor trZeroCutoff r h c X ≤ facI k d r h c chs / 2 ^ 60)
    (hedge : ∀ r h c, edgeI k d r h c x = true → (r, h, c) ∈ W)
    {r : ℕ} {next : List ℤ} (hnext : RowBound W X (r + 1) next) (h : ℕ) :
    trTreeCost trZeroCutoff W r h X ≤ (stateI k d x chs next r h : ℝ) / 2 ^ 72 := by
  set G : ℕ → ℤ := fun c => if edgeI k d r h c x then next.getD (h + c) Q else Q with hGdef
  refine (trTreeCost_le_of_node_bound hW (f := fun c => (facI k d r h c chs : ℝ) / 2 ^ 60)
    (g := fun c => (G c : ℝ) / 2 ^ 72) (fun c hc2 hch => hfac r h c hc2 hch)
    (fun c _ _ => ?_)).trans ?_
  · cases he : edgeI k d r h c x
    · left
      simp only [hGdef, he, Bool.false_eq_true, ↓reduceIte, cast_Q]
      rw [div_self (by positivity)]
    · exact Or.inr ⟨hedge r h c he, by simpa only [hGdef, he, ↓reduceIte] using hnext (h + c)⟩
  rw [sum_Icc_eq_range', stateI]
  have e : ((Q - ((List.range' 2 (trZeroCutoff h - 1)).map fun c : ℕ =>
      wq c * (P - mulUp (facI k d r h c chs) (G c))).sum : ℤ) : ℝ) / 2 ^ 72 =
      1 - ((List.range' 2 (trZeroCutoff h - 1)).map fun c : ℕ =>
        ((wq c * (P - mulUp (facI k d r h c chs) (G c)) : ℤ) : ℝ) / 2 ^ 72).sum := by
    rw [Int.cast_sub, sub_div, cast_sum_map_div, cast_Q, div_self (by positivity)]
  rw [e]
  refine sub_le_sub_left (List.sum_le_sum fun c hc => ?_) 1
  rw [List.mem_range'_1] at hc
  have hc2 : 2 ≤ c := hc.1
  have hc12 : c ≤ 12 := by have := trZeroCutoff_le_twelve h; omega
  have hw0 : (0 : ℝ) ≤ (wq c : ℝ) / 2 ^ 12 := by
    rw [← varpi_eq_wq hc2 hc12]
    exact varpi_nonneg _
  have hprod := le_mulUp (facI k d r h c chs) (G c)
  rw [varpi_eq_wq hc2 hc12]
  calc ((wq c * (P - mulUp (facI k d r h c chs) (G c)) : ℤ) : ℝ) / 2 ^ 72 =
        (wq c : ℝ) / 2 ^ 12 * (1 - (mulUp (facI k d r h c chs) (G c) : ℝ) / 2 ^ 60) := by
        push_cast [cast_P]
        field_simp
    _ ≤ (wq c : ℝ) / 2 ^ 12 *
        (1 - (facI k d r h c chs : ℝ) / 2 ^ 60 * ((G c : ℝ) / 2 ^ 72)) :=
        mul_le_mul_of_nonneg_left (by linarith) hw0

/-- Given factor bounds `facI`, certified continuations in `W` and a row of cost bounds for the
nodes `(r + 1, ·)`, `rowI` is a row of cost bounds for the nodes `(r, ·)`. -/
theorem rowBound_rowI (hW : IsBoundedPolicy W)
    (hfac : ∀ r h c, 2 ≤ c → c ≤ trZeroCutoff h →
      trTreeFactor trZeroCutoff r h c X ≤ facI k d r h c chs / 2 ^ 60)
    (hedge : ∀ r h c, edgeI k d r h c x = true → (r, h, c) ∈ W)
    {r : ℕ} {next : List ℤ} (hnext : RowBound W X (r + 1) next) :
    RowBound W X r (rowI k d x chs next r) := by
  intro h
  by_cases hh : h < 18
  · have : (rowI k d x chs next r).getD h Q =
        if live r h then stateI k d x chs next r h else Q := by
      simp [rowI, List.getD_eq_getElem?_getD, hh]
    rw [this]
    split_ifs
    · exact trTreeCost_le_stateI hW hfac hedge hnext h
    · rw [cast_Q, div_self (by positivity)]
      exact trTreeCost_le_one _ _ _ _ _
  · have : (rowI k d x chs next r).getD h Q = Q := by
      simp [rowI, List.getD_eq_getElem?_getD, show ¬ h < 18 from hh]
    rw [this, cast_Q, div_self (by positivity)]
    exact trTreeCost_le_one _ _ _ _ _

/-- Given factor bounds `facI`, certified continuations in `W` and a row of cost bounds for the
nodes `(n, ·)`, the tree cost at the root is at most `rowsI · 2^{-72}`. -/
theorem trTreeCost_le_rowsI (hW : IsBoundedPolicy W)
    (hfac : ∀ r h c, 2 ≤ c → c ≤ trZeroCutoff h →
      trTreeFactor trZeroCutoff r h c X ≤ facI k d r h c chs / 2 ^ 60)
    (hedge : ∀ r h c, edgeI k d r h c x = true → (r, h, c) ∈ W) (n : ℕ) {next : List ℤ}
    (hnext : RowBound W X n next) :
    trTreeCost trZeroCutoff W 0 0 X ≤ (rowsI k d x chs n next : ℝ) / 2 ^ 72 := by
  induction n generalizing next with
  | zero => exact hnext 0
  | succ n ih =>
    rw [rowsI, forceRow_eq]
    exact ih (rowBound_rowI hW hfac hedge hnext)

end Bound

/-! ### Cells and covers -/

/-- The cost bound, in units `2^{-72}`, for the cell with numerator `x`. -/
def cellV (k d : ℕ) (x : ℤ) : ℤ :=
  rowsI k d x (chainsI x d) 8 (List.replicate 18 Q)

end TrTreeCertificate

end CollatzPosDens
