/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck01
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck02
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck03
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck04
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck05
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck06
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck07
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck08
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck09
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck10
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck11
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck12
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck13
public import CollatzPosDens.Case3.C3H17ValuesDataNodeCheck14

/-!
# The certified table of rounded future costs

By downward induction on `h` from `14` to `1`, the checks of the levels certify the recorded
values: `nodeVal h (J mod 2^15) = 10^8 cf⁺_h(± 3^J)` for every `J`.

## Main results

* `CollatzPosDens.C3H17Values.nodeSpec_h`, `1 ≤ h ≤ 14`: the certified levels.
* `CollatzPosDens.C3H17Values.nodeSpec`: all levels.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

/-- Each of the `16` segments `[2048 p, 2048 p + 2048)` of `[0, 2^15)` satisfies `NodeSegOK`. -/
theorem nodeSegOK_2048 : ∀ p < 2 ^ 15 / 2048, NodeSegOK (2048 * p) 2048 := by
  unfold NodeSegOK
  decide

/-- Level `14` of the certified table: `nodeVal 14 (J mod 2^15) = 10^8 cf⁺_14(± 3^J)`. -/
theorem nodeSpec_14 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 14 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 14 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => absurd h₂ (by omega))
    (fun p hp => nodeCheck_14 p (by norm_num at hp; exact hp))

/-- Level `13` of the certified table: `nodeVal 13 (J mod 2^15) = 10^8 cf⁺_13(± 3^J)`. -/
theorem nodeSpec_13 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 13 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 13 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_13 p (by norm_num at hp; exact hp))

/-- Level `12` of the certified table: `nodeVal 12 (J mod 2^15) = 10^8 cf⁺_12(± 3^J)`. -/
theorem nodeSpec_12 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 12 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 12 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_12 p (by norm_num at hp; exact hp))

/-- Level `11` of the certified table: `nodeVal 11 (J mod 2^15) = 10^8 cf⁺_11(± 3^J)`. -/
theorem nodeSpec_11 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 11 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 11 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_11 p (by norm_num at hp; exact hp))

/-- Level `10` of the certified table: `nodeVal 10 (J mod 2^15) = 10^8 cf⁺_10(± 3^J)`. -/
theorem nodeSpec_10 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 10 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 10 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_10 p (by norm_num at hp; exact hp))

/-- Level `9` of the certified table: `nodeVal 9 (J mod 2^15) = 10^8 cf⁺_9(± 3^J)`. -/
theorem nodeSpec_9 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 9 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 9 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_9 p (by norm_num at hp; exact hp))

/-- Level `8` of the certified table: `nodeVal 8 (J mod 2^15) = 10^8 cf⁺_8(± 3^J)`. -/
theorem nodeSpec_8 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 8 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 8 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_9
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_8 p (by norm_num at hp; exact hp))

/-- Level `7` of the certified table: `nodeVal 7 (J mod 2^15) = 10^8 cf⁺_7(± 3^J)`. -/
theorem nodeSpec_7 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 7 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 7 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_8
      · exact nodeSpec_9
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_7 p (by norm_num at hp; exact hp))

/-- Level `6` of the certified table: `nodeVal 6 (J mod 2^15) = 10^8 cf⁺_6(± 3^J)`. -/
theorem nodeSpec_6 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 6 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 6 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_7
      · exact nodeSpec_8
      · exact nodeSpec_9
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_6 p (by norm_num at hp; exact hp))

/-- Level `5` of the certified table: `nodeVal 5 (J mod 2^15) = 10^8 cf⁺_5(± 3^J)`. -/
theorem nodeSpec_5 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 5 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 5 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_6
      · exact nodeSpec_7
      · exact nodeSpec_8
      · exact nodeSpec_9
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_5 p (by norm_num at hp; exact hp))

/-- Level `4` of the certified table: `nodeVal 4 (J mod 2^15) = 10^8 cf⁺_4(± 3^J)`. -/
theorem nodeSpec_4 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 4 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 4 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_5
      · exact nodeSpec_6
      · exact nodeSpec_7
      · exact nodeSpec_8
      · exact nodeSpec_9
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_4 p (by norm_num at hp; exact hp))

/-- Level `3` of the certified table: `nodeVal 3 (J mod 2^15) = 10^8 cf⁺_3(± 3^J)`. -/
theorem nodeSpec_3 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 3 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 3 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_4
      · exact nodeSpec_5
      · exact nodeSpec_6
      · exact nodeSpec_7
      · exact nodeSpec_8
      · exact nodeSpec_9
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_3 p (by norm_num at hp; exact hp))

/-- Level `2` of the certified table: `nodeVal 2 (J mod 2^15) = 10^8 cf⁺_2(± 3^J)`. -/
theorem nodeSpec_2 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 2 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 2 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_3
      · exact nodeSpec_4
      · exact nodeSpec_5
      · exact nodeSpec_6
      · exact nodeSpec_7
      · exact nodeSpec_8
      · exact nodeSpec_9
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_2 p (by norm_num at hp; exact hp))

/-- Level `1` of the certified table: `nodeVal 1 (J mod 2^15) = 10^8 cf⁺_1(± 3^J)`. -/
theorem nodeSpec_1 : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal 1 (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node 1 (σ * 3 ^ J) :=
  nodeVal_spec_of_checks (n := 2048) (by norm_num) (by norm_num) (by norm_num) nodeSegOK_2048
    (fun h' h₁ h₂ => by
      interval_cases h'
      · exact nodeSpec_2
      · exact nodeSpec_3
      · exact nodeSpec_4
      · exact nodeSpec_5
      · exact nodeSpec_6
      · exact nodeSpec_7
      · exact nodeSpec_8
      · exact nodeSpec_9
      · exact nodeSpec_10
      · exact nodeSpec_11
      · exact nodeSpec_12
      · exact nodeSpec_13
      · exact nodeSpec_14)
    (fun p hp => nodeCheck_1 p (by norm_num at hp; exact hp))

/-- The certified table: `nodeVal h (J mod 2^15) = 10^8 cf⁺_h(± 3^J)` for `1 ≤ h ≤ 14`. -/
theorem nodeSpec {h : ℕ} (h₁ : 1 ≤ h) (h₁₄ : h ≤ 14) : ∀ (J : ℕ) (σ : ℤ), (σ = 1 ∨ σ = -1) →
    (nodeVal h (J % 2 ^ 15) : ℚ) = 10 ^ 8 * c3H17Node h (σ * 3 ^ J) := by
  interval_cases h
  · exact nodeSpec_1
  · exact nodeSpec_2
  · exact nodeSpec_3
  · exact nodeSpec_4
  · exact nodeSpec_5
  · exact nodeSpec_6
  · exact nodeSpec_7
  · exact nodeSpec_8
  · exact nodeSpec_9
  · exact nodeSpec_10
  · exact nodeSpec_11
  · exact nodeSpec_12
  · exact nodeSpec_13
  · exact nodeSpec_14

end C3H17Values

end CollatzPosDens
