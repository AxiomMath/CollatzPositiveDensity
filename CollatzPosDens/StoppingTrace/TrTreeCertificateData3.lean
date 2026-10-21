/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.StoppingTrace.TrTreeCertificateCover

/-!
# The gap-zero certificate: classes modulo `2^4` to `2^16`

Covers of residue classes of odd integers, each checked by the kernel with
`CollatzPosDens.TrTreeCertificate.checkR` and turned into the conclusion
`CollatzPosDens.TrTreeCertificate.Good` by `CollatzPosDens.TrTreeCertificate.good_of_checkR`.

## Main results

* `CollatzPosDens.TrTreeCertificate.good_4_7`
* `CollatzPosDens.TrTreeCertificate.good_7_63`
* `CollatzPosDens.TrTreeCertificate.good_7_79`
* `CollatzPosDens.TrTreeCertificate.good_8_15`
* `CollatzPosDens.TrTreeCertificate.good_9_255`
* `CollatzPosDens.TrTreeCertificate.good_9_369`
* `CollatzPosDens.TrTreeCertificate.good_10_511`
* `CollatzPosDens.TrTreeCertificate.good_10_625`
* `CollatzPosDens.TrTreeCertificate.good_11_911`
* `CollatzPosDens.TrTreeCertificate.good_11_1137`
* `CollatzPosDens.TrTreeCertificate.good_12_1023`
* `CollatzPosDens.TrTreeCertificate.good_12_1025`
* `CollatzPosDens.TrTreeCertificate.good_12_3073`
* `CollatzPosDens.TrTreeCertificate.good_15_16385`
* `CollatzPosDens.TrTreeCertificate.good_16_1`

The theorem with suffix `_k_r` asserts `Good k r`, for the residue class of `r` modulo `2^k`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

namespace TrTreeCertificate

/-- The cover of the class of `7` modulo `2^4`. -/
def cert_4_7 : RT :=
  (.split (.split (.beta (.node .leaf .leaf)) (.beta .leaf)) (.split (.beta (.node .leaf .leaf))
  (.beta (.node .leaf .leaf))))

/-- The certificate conclusion `Good` holds for the class of `7` modulo `2^4`. -/
theorem good_4_7 : Good 4 7 :=
  good_of_checkR cert_4_7 4 7 (by decide +kernel)

/-- The cover of the class of `63` modulo `2^7`. -/
def cert_7_63 : RT :=
  (.split (.split (.beta (.node .leaf .leaf)) (.beta .leaf)) (.split (.beta (.node .leaf .leaf))
  (.beta (.node .leaf (.node .leaf .leaf)))))

/-- The certificate conclusion `Good` holds for the class of `63` modulo `2^7`. -/
theorem good_7_63 : Good 7 63 :=
  good_of_checkR cert_7_63 7 63 (by decide +kernel)

/-- The cover of the class of `79` modulo `2^7`. -/
def cert_7_79 : RT :=
  (.beta (.node .leaf .leaf))

/-- The certificate conclusion `Good` holds for the class of `79` modulo `2^7`. -/
theorem good_7_79 : Good 7 79 :=
  good_of_checkR cert_7_79 7 79 (by decide +kernel)

/-- The cover of the class of `15` modulo `2^8`. -/
def cert_8_15 : RT :=
  (.beta (.node .leaf .leaf))

/-- The certificate conclusion `Good` holds for the class of `15` modulo `2^8`. -/
theorem good_8_15 : Good 8 15 :=
  good_of_checkR cert_8_15 8 15 (by decide +kernel)

/-- The cover of the class of `255` modulo `2^9`. -/
def cert_9_255 : RT :=
  (.split (.beta (.node .leaf (.node .leaf .leaf))) (.beta (.node .leaf (.node .leaf (.node .leaf
  .leaf)))))

/-- The certificate conclusion `Good` holds for the class of `255` modulo `2^9`. -/
theorem good_9_255 : Good 9 255 :=
  good_of_checkR cert_9_255 9 255 (by decide +kernel)

/-- The cover of the class of `369` modulo `2^9`. -/
def cert_9_369 : RT :=
  (.beta (.node .leaf .leaf))

/-- The certificate conclusion `Good` holds for the class of `369` modulo `2^9`. -/
theorem good_9_369 : Good 9 369 :=
  good_of_checkR cert_9_369 9 369 (by decide +kernel)

/-- The cover of the class of `511` modulo `2^10`. -/
def cert_10_511 : RT :=
  (.split (.beta (.node .leaf (.node .leaf .leaf))) (.beta (.node .leaf (.node .leaf .leaf))))

/-- The certificate conclusion `Good` holds for the class of `511` modulo `2^10`. -/
theorem good_10_511 : Good 10 511 :=
  good_of_checkR cert_10_511 10 511 (by decide +kernel)

/-- The cover of the class of `625` modulo `2^10`. -/
def cert_10_625 : RT :=
  (.beta (.node .leaf .leaf))

/-- The certificate conclusion `Good` holds for the class of `625` modulo `2^10`. -/
theorem good_10_625 : Good 10 625 :=
  good_of_checkR cert_10_625 10 625 (by decide +kernel)

/-- The cover of the class of `911` modulo `2^11`. -/
def cert_11_911 : RT :=
  (.beta (.node .leaf .leaf))

/-- The certificate conclusion `Good` holds for the class of `911` modulo `2^11`. -/
theorem good_11_911 : Good 11 911 :=
  good_of_checkR cert_11_911 11 911 (by decide +kernel)

/-- The cover of the class of `1137` modulo `2^11`. -/
def cert_11_1137 : RT :=
  (.beta (.node .leaf .leaf))

/-- The certificate conclusion `Good` holds for the class of `1137` modulo `2^11`. -/
theorem good_11_1137 : Good 11 1137 :=
  good_of_checkR cert_11_1137 11 1137 (by decide +kernel)

/-- The cover of the class of `1023` modulo `2^12`. -/
def cert_12_1023 : RT :=
  (.beta (.node .leaf (.node .leaf .leaf)))

/-- The certificate conclusion `Good` holds for the class of `1023` modulo `2^12`. -/
theorem good_12_1023 : Good 12 1023 :=
  good_of_checkR cert_12_1023 12 1023 (by decide +kernel)

/-- The cover of the class of `1025` modulo `2^12`. -/
def cert_12_1025 : RT :=
  (.beta (.node (.node .leaf .leaf) .leaf))

/-- The certificate conclusion `Good` holds for the class of `1025` modulo `2^12`. -/
theorem good_12_1025 : Good 12 1025 :=
  good_of_checkR cert_12_1025 12 1025 (by decide +kernel)

/-- The cover of the class of `3073` modulo `2^12`. -/
def cert_12_3073 : RT :=
  (.beta (.node (.node .leaf .leaf) .leaf))

/-- The certificate conclusion `Good` holds for the class of `3073` modulo `2^12`. -/
theorem good_12_3073 : Good 12 3073 :=
  good_of_checkR cert_12_3073 12 3073 (by decide +kernel)

/-- The cover of the class of `16385` modulo `2^15`. -/
def cert_15_16385 : RT :=
  (.beta (.node (.node (.node .leaf .leaf) .leaf) .leaf))

/-- The certificate conclusion `Good` holds for the class of `16385` modulo `2^15`. -/
theorem good_15_16385 : Good 15 16385 :=
  good_of_checkR cert_15_16385 15 16385 (by decide +kernel)

/-- The cover of the class of `1` modulo `2^16`. -/
def cert_16_1 : RT :=
  (.split (.beta (.node (.node (.node (.node (.node (.node .leaf .leaf) .leaf) .leaf) .leaf) .leaf)
  .leaf)) .none)

/-- The certificate conclusion `Good` holds for the class of `1` modulo `2^16`. -/
theorem good_16_1 : Good 16 1 :=
  good_of_checkR cert_16_1 16 1 (by decide +kernel)

end TrTreeCertificate

end CollatzPosDens
