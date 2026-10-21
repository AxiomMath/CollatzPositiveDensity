/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02DyadicReduction
public import CollatzPosDens.Seed.S05JointCertExistsGCheck1
public import CollatzPosDens.Seed.S05JointCertExistsGCheck2
public import CollatzPosDens.Seed.S05JointCertExistsGCheck3
public import CollatzPosDens.Seed.S05JointCertExistsGCheck4
public import CollatzPosDens.Seed.S05JointCertExistsYCheck1
public import CollatzPosDens.Seed.S05JointCertExistsYCheck2
public import CollatzPosDens.Seed.S05JointCertExistsYCheck3
public import CollatzPosDens.Seed.S05JointCertExistsYCheck4
public import CollatzPosDens.Seed.S05JointCertExistsYCheck5
public import CollatzPosDens.Seed.S05JointCertExistsYCheck6
public import CollatzPosDens.Seed.S05JointCertExistsYCheck7
public import CollatzPosDens.Seed.S05JointCertExistsYCheck8
public import CollatzPosDens.Seed.S05JointCertExistsYCheck9
public import CollatzPosDens.Seed.S05JointCertExistsYCheck10
public import CollatzPosDens.Seed.S05JointCertExistsYCheck11
public import CollatzPosDens.Seed.S05JointCertExistsYCheck12

/-!
# A joint certificate exists

There are an offset-law certificate `g` and a joint certificate `𝖸` over `g` with
`𝖸_8([6275]_8, 384) ≥ 617014680840434`. Here `[6275]_8 ∈ G_8` is the reduction of the integer
`6275` modulo `3^8 = 6561`.

Both objects are explicit tables of natural numbers. The offset-law table
`g = CollatzPosDens.jointCertG` is `g^{(724)}`, the stationary point of the iteration
`g^{(0)}_k = ⌊2^62 𝖦₀(ξ_k)⌋`,
`g^{(s+1)}_k = max_{l ≤ k} max(g^{(s)}_l, ∑_{a=1}^{60} c_{g^{(s)}}(l, a))`; its entries are
`g_6198 = 4611686018427359570 = ⌊2^62 𝖦₀(ξ_6198)⌋` and `g_384 = 997765252056324269`
(`2^{-62} g_384 = 0.21635…`). The joint table `𝖸 = CollatzPosDens.jointCertY` is computed on
the reachable states: `S_8 = {([6275]_8, 384)}`, and `S_{q-1}` collects the pairs
`(dn_a(r), ι(y_{k,a}))` over `(r, k) ∈ S_q` and the letters `1 ≤ a ≤ 60` with `3 ∣ 2^a r̃ - 1` and
`0 ≤ y_{k,a} ≤ ξ_6198`; for `q = 1, 2, …, 8` in turn, `𝖸_q(r, k)` is the sum
`∑_{a=1}^{60} c^{jt}_{g,𝖸}(q, r, k, a)` on `S_q` and `0` elsewhere. The sets `S_8, …, S_1` have
`1, 26, 243, 1564, 5830, 9719, 8465, 4568` elements, of which `1, 16, 145, 907, 3502, 6076, 5504,
3043` carry a nonzero value, and the top value is `𝖸_8([6275]_8, 384) = 617014680840434`
(`6561 · 2^{-62} · 617014680840434 = 0.87782…`).

## Main results

* `CollatzPosDens.isOfflawCert_jointCertG`: `g` is an offset-law certificate.
* `CollatzPosDens.isJointCert_jointCertY`: `𝖸` is a joint certificate over `g`.
* `CollatzPosDens.exists_isOfflawCert_isJointCert`: a joint certificate exists.

## Implementation notes

The conditions of `CollatzPosDens.IsOfflawCert` are checked index by index by the Boolean checker
`CollatzPosDens.jointCertGCheckAt`, evaluated by the kernel on twelve ranges of indices. The
condition of `CollatzPosDens.IsJointCert` needs checking only at the nonzero entries of `𝖸`
(`CollatzPosDens.isJointCert_iff_of_ne_zero`); each of them is bounded by
`CollatzPosDens.jointCertYCheckAt` by a sum of verified joint contributions read from a witness,
evaluated by the kernel on ranges of entries.

## References

* [Mazur, *Collatz positive density*], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- Every index `k ≤ 6198` passes the checker of the offset-law table. -/
theorem jointCertGRangeOK_all : JointCertGRangeOK 0 6199 :=
  ((((((((((jointCertGRangeOK_0.trans jointCertGRangeOK_512).trans jointCertGRangeOK_1024).trans
    jointCertGRangeOK_1536).trans jointCertGRangeOK_2048).trans jointCertGRangeOK_2560).trans
    jointCertGRangeOK_3072).trans jointCertGRangeOK_3584).trans jointCertGRangeOK_4096).trans
    jointCertGRangeOK_4608).trans jointCertGRangeOK_5120).trans jointCertGRangeOK_5632

/-- The offset-law table `g = jointCertG` is an offset-law certificate. -/
theorem isOfflawCert_jointCertG : IsOfflawCert jointCertG :=
  isOfflawCert_jointCertG_of_rangeOK jointCertGRangeOK_all

/-- Every listed entry of every level `1 ≤ q ≤ 8` of the joint table passes the check. -/
theorem jointCertYLevelOK_all (q : ℕ) (h1 : 1 ≤ q) (h8 : q ≤ 8) :
    JointCertYLevelOK q 0 (jointCertYLen q) := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 := by omega
  · exact
      (((((jointCertYLevelOK_1_0.trans jointCertYLevelOK_1_118).trans
        jointCertYLevelOK_1_630).trans jointCertYLevelOK_1_1142).trans
        jointCertYLevelOK_1_1654).trans jointCertYLevelOK_1_2166).trans
        jointCertYLevelOK_1_2678
  · exact
      (jointCertYLevelOK_2_0.trans jointCertYLevelOK_2_1010).trans jointCertYLevelOK_2_3385
  · exact
      (jointCertYLevelOK_3_0.trans jointCertYLevelOK_3_1465).trans jointCertYLevelOK_3_4419
  · exact
      jointCertYLevelOK_4_0.trans jointCertYLevelOK_4_1988
  · exact
      jointCertYLevelOK_5_0
  · exact
      jointCertYLevelOK_6_0
  · exact
      jointCertYLevelOK_7_0
  · exact
      jointCertYLevelOK_8_0

/-- The joint table `𝖸 = jointCertY` is a joint certificate over `g = jointCertG`. -/
theorem isJointCert_jointCertY : IsJointCert jointCertG jointCertY :=
  isJointCert_jointCertY_of_levelOK jointCertYLevelOK_all

/-- **A joint certificate exists.** There are an offset-law certificate `g` and a joint
certificate `𝖸` over `g` with `𝖸_8([6275]_8, 384) ≥ 617014680840434`. -/
@[collatz_pos_dens "lem_s05_joint_cert_exists"]
theorem exists_isOfflawCert_isJointCert :
    ∃ (g : Fin 6199 → ℕ) (Y : (q : ℕ) → ResidueGroup q → Fin 6199 → ℕ),
      IsOfflawCert g ∧ IsJointCert g Y ∧
        617014680840434 ≤ Y 8 (dyadicRed 8 ⟨((6275 : ℤ) : ℚ), by simp⟩) 384 := by
  refine ⟨jointCertG, jointCertY, isOfflawCert_jointCertG, isJointCert_jointCertY, ?_⟩
  rw [dyadicRed_intCast, Int.cast_ofNat, jointCertY_top]

end CollatzPosDens
