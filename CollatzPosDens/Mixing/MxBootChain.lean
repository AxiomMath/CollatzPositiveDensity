/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxChainRatio
public import CollatzPosDens.Transfer.MxExactProfile
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.RefLaw
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Mixing.MxBootDominate
public import CollatzPosDens.Mixing.MxBootShift
public import CollatzPosDens.Mixing.MxExactProfileAntitone
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxOscTelescope
public import CollatzPosDens.Mixing.MxShJoint
public import CollatzPosDens.Mixing.MxShLocal
public import CollatzPosDens.Mixing.MxShLocalAntitone

/-!
# The exact geometric chain

For every Fourier index `ι` and all integers `n₀ ≤ m ≤ n`, where `n₀ = 2^80` is the mixing gate
level, the reference law `μ_n` satisfies
$$\mathrm{Osc}_{m,n}(\mu_n) \le \mathfrak M^{\mathrm{ex}}_ι(m),$$
where `𝔐^ex_ι` is the exact chained profile.

Write `c = c_bt = 1079/1000` (`bootChainRatio`) for the ratio of the chaining and `Q_ι` for the
local profile `mxShLocal ι` of the shell cut at the index `ι`. The proof is a strong induction on
`n - m`. Put `q = ⌊27 m / 25⌋`; as `m ≥ 1000`, `q ≥ c m > m`. If `n ≤ q`, then `25 n ≤ 27 m` and
`oscillation_refLaw_le_mxShLocal` gives `Osc_{m,n}(μ_n) ≤ Q_ι(n)`; then `Q_ι(n) ≤ Q_ι(m)` by
`mxShLocal_antitone` and `Q_ι(m) ≤ 𝔐^ex_ι(m)` by `mxShLocal_le_mxExactProfile`. Otherwise
`m < q < n`, and splitting the oscillation across the level `q` by `oscillation_refLaw_le_add`,
$$\mathrm{Osc}_{m,n}(\mu_n) \le \mathrm{Osc}_{q,n}(\mu_n) + \mathrm{Osc}_{m,q}(\mu_q)
  \le \mathfrak M^{\mathrm{ex}}_ι(q) + Q_ι(q)
  \le \mathfrak M^{\mathrm{ex}}_ι(c m) + Q_ι(c m) = \mathfrak M^{\mathrm{ex}}_ι(m),$$
by the induction hypothesis for `(q, n)`, `oscillation_refLaw_le_mxShLocal` for `(m, q)`,
`mxExactProfile_antitoneOn` and `mxShLocal_antitone` beyond `n₀ ≤ c m ≤ q`, and the shift
identity `mxExactProfile_shift`.

## Main results

* `CollatzPosDens.oscillation_refLaw_le_mxExactProfile`: `Osc_{m,n}(μ_n) ≤ 𝔐^ex_ι(m)` for
  `n₀ ≤ m ≤ n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026].
-/

@[expose] public section

namespace CollatzPosDens

/-- **The exact geometric chain.** For every Fourier index `ι` and integers `n₀ ≤ m ≤ n`,
`Osc_{m,n}(μ_n) ≤ 𝔐^ex_ι(m)`, where `n₀` is the mixing gate level and `𝔐^ex_ι` the exact
chained profile. -/
@[collatz_pos_dens "lem_mx_boot_chain"]
theorem oscillation_refLaw_le_mxExactProfile (ι : FIndex) {m n : ℕ} (hm : mxGateLevel ≤ m)
    (hmn : m ≤ n) :
    oscillation hmn (fun y => (refLaw n y).toReal) ≤ mxExactProfile ι m := by
  induction h : n - m using Nat.strong_induction_on generalizing m with
  | _ d ih =>
    have hm80 : 2 ^ 80 ≤ m := by rw [← mxGateLevel_def]; exact hm
    have hmR : (mxGateLevel : ℝ) ≤ m := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ m := le_trans (by exact_mod_cast one_le_mxGateLevel) hmR
    set q := 27 * m / 25 with hq
    by_cases hnq : n ≤ q
    · have h25 : 25 * n ≤ 27 * m := by omega
      have hnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hj := oscillation_refLaw_le_mxShLocal ι (hm.trans hmn) hmn h25
      have ha := mxShLocal_antitone ι hmR hnR
      have hD := mxShLocal_le_mxExactProfile ι hm1
      linarith
    · rw [not_le] at hnq
      have hmq : m ≤ q := by omega
      have hqn : q ≤ n := hnq.le
      have hstep : 1079 * m ≤ 1000 * q := by omega
      have hcq : (bootChainRatio : ℝ) * m ≤ q := by
        have : ((1079 * m : ℕ) : ℝ) ≤ ((1000 * q : ℕ) : ℝ) := by exact_mod_cast hstep
        push_cast at this
        rw [bootChainRatio_cast]
        linarith
      have hcm : (mxGateLevel : ℝ) ≤ (bootChainRatio : ℝ) * m := by
        rw [bootChainRatio_cast]
        have : (0 : ℝ) ≤ m := by linarith
        linarith
      have hq25 : 25 * q ≤ 27 * m := by omega
      have hqg : mxGateLevel ≤ q := hm.trans hmq
      have hIH := ih (n - q) (by omega) hqg hqn rfl
      have hj := oscillation_refLaw_le_mxShLocal ι hqg hmq hq25
      have hPa := mxExactProfile_antitoneOn ι hcm hcq
      have hQa := mxShLocal_antitone ι hcm hcq
      have hS := mxExactProfile_shift ι (x := (m : ℝ)) (by linarith)
      have hT := oscillation_refLaw_le_add hmq hqn
      linarith

end CollatzPosDens
