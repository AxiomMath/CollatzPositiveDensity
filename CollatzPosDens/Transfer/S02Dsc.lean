/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.S02OmegaFar

/-!
# The scale threshold `D_sc`

The scale threshold at the Fourier parameter index `ι ∈ {o, b}` is the natural number
$$D_{\mathrm{sc}}(o) := 2 + P_*(o) + \lceil 2\,\Omega_{\mathrm{far}}(o) / 3 \rceil, \qquad
D_{\mathrm{sc}}(b) := 2 + P_*(b) + \lceil \Omega_{\mathrm{far}}(b) / 2 \rceil,$$
built from the final time `P_*(ι)` and the far-gap threshold `Ω_far(ι)`. It is at least `2` and
at least `P_*(ι)` at every index; at `o` three times it is at least `2 Ω_far(o)`, and at every
index twice it is at least `Ω_far(ι)`.

## Main definitions

* `CollatzPosDens.Dsc`: the scale threshold `D_sc(ι)`.

## Main results

* `CollatzPosDens.Dsc_o_def`, `CollatzPosDens.Dsc_b_def`: the defining formulas
  `D_sc(o) = 2 + P_*(o) + (2 Ω_far(o) + 2) / 3` and `D_sc(b) = 2 + P_*(b) + (Ω_far(b) + 1) / 2`
  (natural-number division).
* `CollatzPosDens.Dsc_o_eq_ceil`, `CollatzPosDens.Dsc_b_eq_ceil`: the same with the ceilings
  `⌈2 Ω_far(o) / 3⌉` and `⌈Ω_far(b) / 2⌉` over `ℚ`.
* `CollatzPosDens.cast_Dsc_o`, `CollatzPosDens.cast_Dsc_b`: the same formulas cast into a
  semiring, e.g. `ℝ`.
* `CollatzPosDens.two_le_Dsc`, `CollatzPosDens.Dsc_pos`, `CollatzPosDens.Dsc_ne_zero`:
  `2 ≤ D_sc(ι)`, `0 < D_sc(ι)` and `D_sc(ι) ≠ 0`.
* `CollatzPosDens.pStar_le_Dsc`, `CollatzPosDens.pStar_add_two_le_Dsc`:
  `P_*(ι) ≤ D_sc(ι)` and `P_*(ι) + 2 ≤ D_sc(ι)`.
* `CollatzPosDens.two_mul_omegaFar_le_three_mul_Dsc_o`: `2 Ω_far(o) ≤ 3 D_sc(o)`.
* `CollatzPosDens.omegaFar_le_two_mul_Dsc`: `Ω_far(ι) ≤ 2 D_sc(ι)`.

## Implementation notes

Since `P_*(ι)` and `Ω_far(ι)` are closed natural numbers too large to be normalised to numerals
casually, `D_sc` is declared irreducible and is used only through its defining lemmas, never by
evaluation. Its body is the value of the auxiliary function `DscAux ι p w` of free variables
(`2 + p + (2 w + 2) / 3` at `o`, `2 + p + (w + 1) / 2` at `b`), so that the defining equations
are checked with the arguments free and the kernel never tries to normalise the closed sum.

The ceilings `⌈2 w / 3⌉` and `⌈w / 2⌉` of a natural number `w` are written in natural-number
arithmetic as `(2 w + 2) / 3` and `(w + 1) / 2`; `Dsc_o_eq_ceil` and `Dsc_b_eq_ceil` recover the
ceilings over `ℚ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale threshold as a function of free variables: `DscAux o p w = 2 + p + ⌈2 w / 3⌉` and
`DscAux b p w = 2 + p + ⌈w / 2⌉`, the ceilings written as `(2 w + 2) / 3` and `(w + 1) / 2`; the
scale threshold is `D_sc(ι) = DscAux ι P_*(ι) Ω_far(ι)`. -/
def DscAux : FIndex → ℕ → ℕ → ℕ
  | .o, p, w => 2 + p + (2 * w + 2) / 3
  | .b, p, w => 2 + p + (w + 1) / 2

/-- The defining formula of `DscAux` at the original index. -/
theorem DscAux_o (p w : ℕ) : DscAux .o p w = 2 + p + (2 * w + 2) / 3 := rfl

/-- The defining formula of `DscAux` at the bootstrap index. -/
theorem DscAux_b (p w : ℕ) : DscAux .b p w = 2 + p + (w + 1) / 2 := rfl

/-- The scale threshold `D_sc(o) := 2 + P_*(o) + ⌈2 Ω_far(o) / 3⌉` and
`D_sc(b) := 2 + P_*(b) + ⌈Ω_far(b) / 2⌉`, in `ℕ`. -/
@[collatz_pos_dens "def_s02_Dsc", irreducible]
noncomputable def Dsc (ι : FIndex) : ℕ := DscAux ι (pStar ι) (omegaFar ι)

/-- The defining formula of `D_sc(o)`, the ceiling `⌈2 Ω_far(o) / 3⌉` written in natural-number
division as `(2 Ω_far(o) + 2) / 3`. -/
theorem Dsc_o_def : Dsc .o = 2 + pStar .o + (2 * omegaFar .o + 2) / 3 := by
  delta Dsc
  exact DscAux_o _ _

/-- The defining formula of `D_sc(b)`, the ceiling `⌈Ω_far(b) / 2⌉` written in natural-number
division as `(Ω_far(b) + 1) / 2`. -/
theorem Dsc_b_def : Dsc .b = 2 + pStar .b + (omegaFar .b + 1) / 2 := by
  delta Dsc
  exact DscAux_b _ _

/-- For a natural number `w`, `⌈w / 2⌉ = (w + 1) / 2`. -/
private theorem natCeil_half_eq_dsc (w : ℕ) : ⌈(w : ℚ) / 2⌉₊ = (w + 1) / 2 := by
  rcases Nat.even_or_odd' w with ⟨k, rfl | rfl⟩
  · rw [show ((2 * k : ℕ) : ℚ) / 2 = (k : ℕ) by push_cast; ring, Nat.ceil_natCast]
    omega
  · rw [Nat.ceil_eq_iff (by omega)]
    have h : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [h]
    push_cast
    constructor <;> linarith

/-- For a natural number `w`, `⌈2 w / 3⌉ = (2 w + 2) / 3`. -/
private theorem natCeil_two_mul_div_three_eq_dsc (w : ℕ) :
    ⌈2 * (w : ℚ) / 3⌉₊ = (2 * w + 2) / 3 := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  have hq : (((2 * w + 2) / 3 : ℕ) : ℚ) * 3 + (((2 * w + 2) % 3 : ℕ) : ℚ) = 2 * w + 2 := by
    exact_mod_cast (by omega : (2 * w + 2) / 3 * 3 + (2 * w + 2) % 3 = 2 * w + 2)
  have hr : (((2 * w + 2) % 3 : ℕ) : ℚ) ≤ 2 := by exact_mod_cast (by omega : (2 * w + 2) % 3 ≤ 2)
  have hr0 : (0 : ℚ) ≤ (((2 * w + 2) % 3 : ℕ) : ℚ) := Nat.cast_nonneg _
  rw [Nat.ceil_eq_iff (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_le_iff₀ (by norm_num)]
    linarith

/-- The defining formula of `D_sc(o)` with the ceiling over `ℚ`:
`D_sc(o) = 2 + P_*(o) + ⌈2 Ω_far(o) / 3⌉`. -/
theorem Dsc_o_eq_ceil : Dsc .o = 2 + pStar .o + ⌈2 * (omegaFar .o : ℚ) / 3⌉₊ := by
  rw [Dsc_o_def, natCeil_two_mul_div_three_eq_dsc]

/-- The defining formula of `D_sc(b)` with the ceiling over `ℚ`:
`D_sc(b) = 2 + P_*(b) + ⌈Ω_far(b) / 2⌉`. -/
theorem Dsc_b_eq_ceil : Dsc .b = 2 + pStar .b + ⌈(omegaFar .b : ℚ) / 2⌉₊ := by
  rw [Dsc_b_def, natCeil_half_eq_dsc]

/-- The defining formula of `D_sc(o)`, cast into a semiring. -/
@[simp, norm_cast]
theorem cast_Dsc_o {R : Type*} [Semiring R] :
    (Dsc .o : R) = 2 + (pStar .o : R) + (((2 * omegaFar .o + 2) / 3 : ℕ) : R) := by
  rw [Dsc_o_def]
  push_cast
  rfl

/-- The defining formula of `D_sc(b)`, cast into a semiring. -/
@[simp, norm_cast]
theorem cast_Dsc_b {R : Type*} [Semiring R] :
    (Dsc .b : R) = 2 + (pStar .b : R) + (((omegaFar .b + 1) / 2 : ℕ) : R) := by
  rw [Dsc_b_def]
  push_cast
  rfl

/-- `D_sc(ι) = 2 + P_*(ι) + x` with `x` the index-dependent far-gap summand. -/
private theorem exists_Dsc_eq (ι : FIndex) : ∃ x, Dsc ι = 2 + pStar ι + x := by
  cases ι
  · exact ⟨_, Dsc_o_def⟩
  · exact ⟨_, Dsc_b_def⟩

/-- `P_*(ι) + 2 ≤ D_sc(ι)`. -/
theorem pStar_add_two_le_Dsc (ι : FIndex) : pStar ι + 2 ≤ Dsc ι := by
  obtain ⟨x, hx⟩ := exists_Dsc_eq ι
  omega

/-- `2 ≤ D_sc(ι)`. -/
theorem two_le_Dsc (ι : FIndex) : 2 ≤ Dsc ι := by
  have := pStar_add_two_le_Dsc ι
  omega

/-- `D_sc(ι)` is positive. -/
theorem Dsc_pos (ι : FIndex) : 0 < Dsc ι := lt_of_lt_of_le two_pos (two_le_Dsc ι)

/-- `D_sc(ι) ≠ 0`. -/
theorem Dsc_ne_zero (ι : FIndex) : Dsc ι ≠ 0 := (Dsc_pos ι).ne'

/-- `P_*(ι) ≤ D_sc(ι)`. -/
theorem pStar_le_Dsc (ι : FIndex) : pStar ι ≤ Dsc ι := by
  have := pStar_add_two_le_Dsc ι
  omega

/-- At the original index, `2 Ω_far(o) ≤ 3 D_sc(o)`. -/
theorem two_mul_omegaFar_le_three_mul_Dsc_o : 2 * omegaFar .o ≤ 3 * Dsc .o := by
  rw [Dsc_o_def]
  omega

/-- `Ω_far(ι) ≤ 2 D_sc(ι)` at every index. -/
theorem omegaFar_le_two_mul_Dsc (ι : FIndex) : omegaFar ι ≤ 2 * Dsc ι := by
  cases ι
  · have := two_mul_omegaFar_le_three_mul_Dsc_o
    omega
  · rw [Dsc_b_def]
    omega

end CollatzPosDens
