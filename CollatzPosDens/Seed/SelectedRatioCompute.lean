/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.BarrierNat
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Lb

/-!
# Mass retained by the selector: the exact enumeration

This file contains the computational half of the proof that the five-block selector retains
more than half of the mass of the first five central families: an exact, kernel-checked
enumeration of the families `𝒞(u, 16)`, `9 ≤ u ≤ 13`.

A family of words `(a₁, …, a_s)` whose membership is decided by first-crossing conditions on
the prefix sums `A_i = a₁ + ⋯ + a_i` is enumerated by a backward dynamic programme over the
states `(d, A)` (a prefix of length `d` with sum `A`). The weight `2^{top - A}` of a word is
accumulated together with a formal power `X^z`, where `z = ∑ ⌈2^p 3^{i-1} 2^{-A_i}⌉` is the
rounded offset at precision `p`; evaluating at `X = 2^k` packs the whole distribution of `z`
into one natural number, whose base-`X` digits are then read off. All arithmetic is exact
natural-number arithmetic on literals, so the values below are proved by `decide +kernel`.

## Main definitions

* `CollatzPosDens.SelectedRatio.Par`: the parameters of a first-crossing family.
* `CollatzPosDens.SelectedRatio.Par.dpRoot`: the dynamic programme.
* `CollatzPosDens.SelectedRatio.mass`, `nu`, `P01`: the computed masses.

## Main results

* `CollatzPosDens.SelectedRatio.mass_nine` … `mass_thirteen`: the masses
  `2^{top} 𝐩(𝒞(u, 16))`.
* `CollatzPosDens.SelectedRatio.nu_eleven`, `nu_twelve`, `nu_thirteen`: the selected
  masses of `𝒞(11, 16)`, `𝒞(12, 16)`, `𝒞(13, 16)`.
* `CollatzPosDens.SelectedRatio.P01_eq`: the selected joint mass of
  `𝒞(9, 16) × 𝒞(10, 16)`.

## Implementation notes

The correctness of the programme (that the computed numbers are the sums over the families)
is proved in `CollatzPosDens.Seed.SelectedRatio`; this file only evaluates. It is
kept separate, with light imports, so that the kernel evaluation runs in a small process. The
evaluated definitions are irreducible, so that the elaborator never attempts to unfold them;
the kernel, which `decide +kernel` uses, ignores this attribute.

The digit bases are chosen so that no digit overflows: `X0 = 2^64` exceeds every
`2^{top} 𝐩(𝒞(u, 16))`, `X1 = 2^46` exceeds `2^{46} 𝐩(𝒞(10, 16))`, and `X2 = 2^100` exceeds
`1217 · 2^{46} · 2^{42} 𝐩(𝒞(9, 16))`. In `F9` the positions `z` with `192 ≤ z < st d A`, where
every admissible second block is selected, are summed in closed form.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens.SelectedRatio

/-- Parameters of a first-crossing family: lengths `l < s ≤ h`, prefix barrier `H`, final
window `lo ≤ A ≤ hi`, and a bound `top` on all valuation sums. -/
structure Par where
  /-- lower length bound -/
  l : ℕ
  /-- upper length bound -/
  h : ℕ
  /-- bound on valuation sums -/
  top : ℕ
  /-- barrier -/
  H : ℕ → ℤ
  /-- lower end of the final window -/
  lo : ℕ → ℤ
  /-- upper end of the final window -/
  hi : ℕ → ℤ

/-- A state `(d, A)` is final. -/
abbrev Par.Fin (P : Par) (d A : ℕ) : Prop :=
  P.l < d ∧ d ≤ P.h ∧ P.lo d ≤ A ∧ (A : ℤ) ≤ P.hi d ∧ A ≤ P.top

/-- A state `(d, A)` may be extended. -/
abbrev Par.Alive (P : Par) (d A : ℕ) : Prop :=
  P.l ≤ d → (A : ℤ) < P.H d

/-- One level of the programme, processing the next level's values `[n_A, …, n_top]`. -/
def Par.goRow (P : Par) (pw : ℕ → ℕ → ℕ) (M : ℕ) (F : ℕ → ℕ → ℕ) (d : ℕ) :
    ℕ → List ℕ → ℕ × List ℕ
  | _, [] => (0, [])
  | A, x :: L =>
    let r := P.goRow pw M F d (A + 1) L
    ((pw d A * x + r.1) % M,
      ((if P.Fin d A then 2 ^ (P.top - A) * F d A else 0) +
        (if P.Alive d A then r.1 else 0)) % M :: r.2)

/-- The table of the programme at level `h + 1 - k`. -/
def Par.table (P : Par) (pw : ℕ → ℕ → ℕ) (M : ℕ) (F : ℕ → ℕ → ℕ) : ℕ → List ℕ
  | 0 => List.replicate (P.top + 1) 0
  | k + 1 => (P.goRow pw M F (P.h - k) 0 (P.table pw M F k)).2

/-- The value of the programme at the root state `(0, 0)`. -/
def Par.dpRoot (P : Par) (pw : ℕ → ℕ → ℕ) (M : ℕ) (F : ℕ → ℕ → ℕ) : ℕ :=
  (P.table pw M F (P.h + 1)).headD 0

/-- The sum of the base-`X` digits of `N` in positions `lo, …, hi`, computed modulo `X - 1`. -/
def dig (X N lo hi : ℕ) : ℕ := N % X ^ (hi + 1) / X ^ lo % (X - 1)

/-- The transition multiplier `X ^ min (inc j a) E`. -/
def pw (X : ℕ) (inc : ℕ → ℕ → ℕ) (E j a : ℕ) : ℕ := X ^ min (inc j a) E

/-- The minimal early overshoot `μ_u(s)`, by search. -/
def mu (u s : ℕ) : ℕ :=
  ((List.range 64).find? fun k : ℕ => decide (16 * 3 ^ s * 2 ^ (3 * u) <
    (2 ^ (3 * u) - 1) * 2 ^ (barrierRb u s + (k : ℤ)).toNat)).getD 0

/-- The parameters of `𝒞(u, 16)` for `9 ≤ u ≤ 13`. -/
def par (u : ℕ) : Par where
  l := lb u
  h := hb u
  top := (barrierRb u (hb u) + 16).toNat
  H := barrierRb u
  lo s := barrierRb u s + if u ≤ 11 then (mu u s : ℤ) else 0
  hi s := barrierRb u s + 16

/-- The rounded increment `⌈2^pp 3^j / 2^(A + q)⌉`. -/
def inc (pp q j A : ℕ) : ℕ := (2 ^ pp * 3 ^ j + 2 ^ (A + q) - 1) / 2 ^ (A + q)

/-- `2^{top} 𝐩(𝒞(u, 16))`. -/
@[irreducible] def mass (u : ℕ) : ℕ := (par u).dpRoot (fun _ _ => 1) 0 (fun _ _ => 1)

/-- The digit base for the selected single families. -/
def X0 : ℕ := 2 ^ 64

/-- The digit base for the second block of the joint computation. -/
def X1 : ℕ := 2 ^ 46

/-- The mass of the words of `𝒞(u, 16)` with `2^p rd_p ≤ cap`, scaled by `2^{top}`. -/
@[irreducible] def nu (u pp q cap : ℕ) : ℕ :=
  dig X0 ((par u).dpRoot (pw X0 (inc pp q) (cap + 1)) (X0 ^ (cap + 1)) (fun _ _ => 1)) 0 cap

/-- The packed distribution of `2^6 rd_6` on `𝒞(10, 16)`. -/
@[irreducible] def NG : ℕ := (par 10).dpRoot (pw X1 (inc 6 0) 1025) (X1 ^ 1025) (fun _ _ => 1)

/-- The least admissible `2^6 rd_6(v₁)` for a first block with data `(d, A, z)`. -/
def lo (d A z : ℕ) : ℕ :=
  if 192 ≤ z then 0 else ((192 - z) * 2 ^ A + 8 * 3 ^ d - 1) / (8 * 3 ^ d)

/-- The largest admissible `2^6 rd_6(v₁)` for a first block with data `(d, A, z)`. -/
def hi (d A z : ℕ) : ℕ := min 1024 ((1216 - z) * 2 ^ A / (8 * 3 ^ d))

/-- The mass of the admissible second blocks, scaled by `2^{46}`. -/
@[irreducible] def T (d A z : ℕ) : ℕ :=
  if 1216 < z ∨ hi d A z < lo d A z then 0 else dig X1 NG (lo d A z) (hi d A z)

/-- The digit base for the joint computation. -/
def X2 : ℕ := 2 ^ 100

/-- `∑_{z ∈ L} f z X^{1216 - z}`, skipping the vanishing terms. -/
def skipSum (f : ℕ → ℕ) (X : ℕ) : List ℕ → ℕ
  | [] => 0
  | z :: L => if f z = 0 then skipSum f X L else f z * X ^ (1216 - z) + skipSum f X L

/-- `⌈1024 · 8 · 3^d / 2^A⌉`. -/
def m (d A : ℕ) : ℕ := (1024 * (8 * 3 ^ d) + 2 ^ A - 1) / 2 ^ A

/-- The start of the upper partial region. -/
def st (d A : ℕ) : ℕ := max 192 (1217 - m d A)

/-- `∑_{i < n} X^{1024 - i}`, in closed form. -/
def geo (X n : ℕ) : ℕ := (X ^ 1025 - 1) / (X - 1) - (X ^ (1025 - n) - 1) / (X - 1)

/-- The packed terminal weight `∑_{z ≤ 1216} T(d, A, z) X^{1216 - z}`, computed in three
regions. -/
@[irreducible] def F9 (d A : ℕ) : ℕ :=
  skipSum (T d A) X2 (List.range' 0 192) +
  dig X1 NG 0 1024 * geo X2 (st d A - 192) +
  skipSum (T d A) X2 (List.range' (st d A) (1217 - st d A))

/-- The packed joint programme on `𝒞(9, 16)`. -/
@[irreducible] def N9 : ℕ := (par 9).dpRoot (pw X2 (inc 9 0) 1217) (X2 ^ 1217) F9

/-- The selected joint mass, scaled by `2^{88}`. -/
@[irreducible] def P01 : ℕ := dig X2 N9 1216 1216

/-- The value of `mass 9`. -/
theorem mass_nine : mass 9 = 1121528720843 := by decide +kernel

/-- The value of `mass 10`. -/
theorem mass_ten : mass 10 = 25912441038107 := by decide +kernel

/-- The value of `mass 11`. -/
theorem mass_eleven : mass 11 = 110172925800689 := by decide +kernel

/-- The value of `mass 12`. -/
theorem mass_twelve : mass 12 = 2156388303073866 := by decide +kernel

/-- The value of `mass 13`. -/
theorem mass_thirteen : mass 13 = 8200094289238498 := by decide +kernel

/-- The value of `nu 11 3 0 128`. -/
theorem nu_eleven : nu 11 3 0 128 = 108161817817367 := by decide +kernel

/-- The value of `nu 12 0 0 64`. -/
theorem nu_twelve : nu 12 0 0 64 = 2155020659894667 := by decide +kernel

/-- The value of `nu 13 0 3 32`. -/
theorem nu_thirteen : nu 13 0 3 32 = 8199875792177575 := by decide +kernel

/-- The value of `P01`. -/
theorem P01_eq : P01 = 15856838138131582931885054 := by decide +kernel

end CollatzPosDens.SelectedRatio
