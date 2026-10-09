/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.ZMod.Basic
public import CollatzPosDens.Attr

/-!
# Base-four repunits meet every residue class modulo a power of three

For `v ≥ 0` put `r_v = (4^v - 1)/3 = 1 + 4 + ⋯ + 4^{v-1}`. For all `a, q ≥ 0`, the `3^q`
values `r_v` with `a ≤ v < a + 3^q` are pairwise incongruent modulo `3^q`, hence meet every
residue class modulo `3^q`.

The proof uses the lifting-the-exponent lemma: for `c ≥ 1`,
`v₃(4^c - 1) = 1 + v₃(c)`. If `a ≤ v < v' < a + 3^q` and `c = v' - v`, then
`3 (r_{v'} - r_v) = 4^v (4^c - 1)` and `v₃(c) < q`, so `3^q ∤ r_{v'} - r_v`.

## Main results

* `CollatzPosDens.not_pow_succ_dvd_four_pow_sub_one`: `3^{q+1} ∤ 4^c - 1` for `0 < c < 3^q`.
* `CollatzPosDens.exists_four_pow_sub_one_div_three_modEq`: every residue class modulo `3^q`
  contains some `(4^v - 1)/3` with `a ≤ v < a + 3^q`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `0 < c < 3^q`, the power `3^{q+1}` does not divide `4^c - 1`: by lifting the exponent,
`v₃(4^c - 1) = 1 + v₃(c)` and `v₃(c) < q`. -/
theorem not_pow_succ_dvd_four_pow_sub_one {q c : ℕ} (hc : 0 < c) (hcq : c < 3 ^ q) :
    ¬ (3 : ℤ) ^ (q + 1) ∣ 4 ^ c - 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  have h1 : 1 < 4 ^ c := Nat.one_lt_pow hc.ne' (by norm_num)
  have hN : 3 ^ (q + 1) ∣ 4 ^ c - 1 := by
    exact_mod_cast (show ((3 ^ (q + 1) : ℕ) : ℤ) ∣ ((4 ^ c - 1 : ℕ) : ℤ) by
      push_cast [h1.le]
      exact h)
  have hval : padicValNat 3 (4 ^ c - 1 ^ c) = padicValNat 3 (4 - 1) + padicValNat 3 c :=
    padicValNat.pow_sub_pow (by decide) (by norm_num) (by norm_num) (by norm_num) hc.ne'
  norm_num at hval
  rw [padicValNat_dvd_iff_le (by omega), hval] at hN
  have hcv : 3 ^ q ∣ c := (pow_dvd_pow 3 (by omega)).trans pow_padicValNat_dvd
  exact absurd (Nat.le_of_dvd hc hcv) (by omega)

/-- **Repunit residues.** For all `a q : ℕ` and every integer `y` there is `v` with
`a ≤ v < a + 3^q` and `(4^v - 1)/3 ≡ y [ZMOD 3^q]`. -/
@[collatz_pos_dens "lem_repunit_residues"]
theorem exists_four_pow_sub_one_div_three_modEq (a q : ℕ) (y : ℤ) :
    ∃ v : ℕ, a ≤ v ∧ v < a + 3 ^ q ∧ ((4 : ℤ) ^ v - 1) / 3 ≡ y [ZMOD 3 ^ q] := by
  have hr : ∀ v : ℕ, 3 * (((4 : ℤ) ^ v - 1) / 3) = 4 ^ v - 1 := fun v =>
    Int.mul_ediv_cancel' (by simpa using sub_dvd_pow_sub_pow (4 : ℤ) 1 v)
  have key : ∀ v v', a ≤ v → v < v' → v' < a + 3 ^ q →
      ¬ (3 : ℤ) ^ q ∣ ((4 : ℤ) ^ v' - 1) / 3 - ((4 : ℤ) ^ v - 1) / 3 := by
    intro v v' hav hvv' hv' h
    have h3 := mul_dvd_mul_left (3 : ℤ) h
    rw [mul_sub, hr, hr, ← pow_succ'] at h3
    have he : (4 : ℤ) ^ v' - 1 - (4 ^ v - 1) = 4 ^ v * (4 ^ (v' - v) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hvv'.le]
      ring
    rw [he] at h3
    have hcop : IsCoprime ((3 : ℤ) ^ (q + 1)) (4 ^ v) :=
      (show IsCoprime (3 : ℤ) 4 from ⟨-1, 1, by norm_num⟩).pow
    exact not_pow_succ_dvd_four_pow_sub_one (q := q) (c := v' - v) (by omega) (by omega)
      (hcop.dvd_of_dvd_mul_left h3)
  let f : ∀ v ∈ Finset.Ico a (a + 3 ^ q), ZMod (3 ^ q) :=
    fun v _ => ((((4 : ℤ) ^ v - 1) / 3 : ℤ) : ZMod (3 ^ q))
  have hinj : ∀ v₁ v₂ h₁ h₂, f v₁ h₁ = f v₂ h₂ → v₁ = v₂ := by
    intro v₁ v₂ h₁ h₂ he
    simp only [f, Finset.mem_Ico] at h₁ h₂ he
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at he
    rcases lt_trichotomy v₁ v₂ with hlt | heq | hgt
    · exact absurd he (key _ _ h₁.1 hlt h₂.2)
    · exact heq
    · exact absurd (dvd_sub_comm.mp he) (key _ _ h₂.1 hgt h₁.2)
  obtain ⟨v, hv, hvy⟩ := Finset.surj_on_of_inj_on_of_card_le f
    (fun _ _ => Finset.mem_univ _) hinj (by simp) (y : ZMod (3 ^ q)) (Finset.mem_univ _)
  rw [Finset.mem_Ico] at hv
  exact ⟨v, hv.1, hv.2, ((ZMod.intCast_eq_intCast_iff _ _ _).mp hvy).symm⟩

end CollatzPosDens
