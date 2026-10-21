/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.StoppingTrace.TrTreeCertificateCover

/-!
# The gap-zero certificate, part 2 of 3

The covers of 15 residue classes, each checked by the kernel with
`CollatzPosDens.TrTreeCertificate.checkR` and turned into the conclusion
`CollatzPosDens.TrTreeCertificate.Good` of the certificate by
`CollatzPosDens.TrTreeCertificate.good_of_checkR`. The classes of all parts together, assembled in
`CollatzPosDens.trTreeCost_sub_trTailGain_lt`, cover every odd integer.

## Main results

* `CollatzPosDens.TrTreeCertificate.good_3_5`, …, `CollatzPosDens.TrTreeCertificate.good_15_32767`:
  the conclusion `Good k r` of the certificate for the residue class of `r` modulo `2^k`, for each
  class of this part.

## References

* [Mazur, *Collatz positive density*], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrTreeCertificate

/-- The cover of the class of `5` modulo `2^3`. -/
def cert_3_5 : RT :=
  (.split (.split (.beta .leaf) (.beta .leaf)) (.beta .leaf))

/-- The conclusion of the certificate holds for the class of `5` modulo `2^3`. -/
theorem good_3_5 : Good 3 5 :=
  good_of_checkR cert_3_5 3 5 (by decide +kernel)

/-- The cover of the class of `17` modulo `2^6`. -/
def cert_6_17 : RT :=
  (.split (.beta (.node (.node .leaf .leaf) .leaf)) (.beta (.node (.node .leaf .leaf) .leaf)))

/-- The conclusion of the certificate holds for the class of `17` modulo `2^6`. -/
theorem good_6_17 : Good 6 17 :=
  good_of_checkR cert_6_17 6 17 (by decide +kernel)

/-- The cover of the class of `33` modulo `2^6`. -/
def cert_6_33 : RT :=
  (.split (.split (.beta (.node (.node .leaf .leaf) .leaf)) (.beta (.node (.node .leaf .leaf)
  .leaf))) (.split (.beta (.node .leaf .leaf)) (.beta (.node (.node .leaf .leaf) .leaf))))

/-- The conclusion of the certificate holds for the class of `33` modulo `2^6`. -/
theorem good_6_33 : Good 6 33 :=
  good_of_checkR cert_6_33 6 33 (by decide +kernel)

/-- The cover of the class of `47` modulo `2^6`. -/
def cert_6_47 : RT :=
  (.split (.beta (.node .leaf (.node .leaf .leaf))) (.beta (.node .leaf (.node .leaf .leaf))))

/-- The conclusion of the certificate holds for the class of `47` modulo `2^6`. -/
theorem good_6_47 : Good 6 47 :=
  good_of_checkR cert_6_47 6 47 (by decide +kernel)

/-- The cover of the class of `49` modulo `2^7`. -/
def cert_7_49 : RT :=
  (.beta (.node .leaf .leaf))

/-- The conclusion of the certificate holds for the class of `49` modulo `2^7`. -/
theorem good_7_49 : Good 7 49 :=
  good_of_checkR cert_7_49 7 49 (by decide +kernel)

/-- The cover of the class of `127` modulo `2^8`. -/
def cert_8_127 : RT :=
  (.split (.split (.beta (.node .leaf (.node .leaf .leaf))) (.beta (.node .leaf .leaf))) (.split
  (.beta (.node .leaf (.node .leaf .leaf))) (.beta (.node .leaf (.node .leaf .leaf)))))

/-- The conclusion of the certificate holds for the class of `127` modulo `2^8`. -/
theorem good_8_127 : Good 8 127 :=
  good_of_checkR cert_8_127 8 127 (by decide +kernel)

/-- The cover of the class of `143` modulo `2^9`. -/
def cert_9_143 : RT :=
  (.beta (.node .leaf .leaf))

/-- The conclusion of the certificate holds for the class of `143` modulo `2^9`. -/
theorem good_9_143 : Good 9 143 :=
  good_of_checkR cert_9_143 9 143 (by decide +kernel)

/-- The cover of the class of `1935` modulo `2^11`. -/
def cert_11_1935 : RT :=
  (.beta (.node .leaf .leaf))

/-- The conclusion of the certificate holds for the class of `1935` modulo `2^11`. -/
theorem good_11_1935 : Good 11 1935 :=
  good_of_checkR cert_11_1935 11 1935 (by decide +kernel)

/-- The cover of the class of `3071` modulo `2^12`. -/
def cert_12_3071 : RT :=
  (.beta (.node .leaf (.node .leaf .leaf)))

/-- The conclusion of the certificate holds for the class of `3071` modulo `2^12`. -/
theorem good_12_3071 : Good 12 3071 :=
  good_of_checkR cert_12_3071 12 3071 (by decide +kernel)

/-- The cover of the class of `2047` modulo `2^13`. -/
def cert_13_2047 : RT :=
  (.beta (.node .leaf (.node .leaf .leaf)))

/-- The conclusion of the certificate holds for the class of `2047` modulo `2^13`. -/
theorem good_13_2047 : Good 13 2047 :=
  good_of_checkR cert_13_2047 13 2047 (by decide +kernel)

/-- The cover of the class of `4095` modulo `2^13`. -/
def cert_13_4095 : RT :=
  (.beta (.node .leaf (.node .leaf (.node .leaf (.node .leaf .leaf)))))

/-- The conclusion of the certificate holds for the class of `4095` modulo `2^13`. -/
theorem good_13_4095 : Good 13 4095 :=
  good_of_checkR cert_13_4095 13 4095 (by decide +kernel)

/-- The cover of the class of `6143` modulo `2^13`. -/
def cert_13_6143 : RT :=
  (.beta (.node .leaf (.node .leaf .leaf)))

/-- The conclusion of the certificate holds for the class of `6143` modulo `2^13`. -/
theorem good_13_6143 : Good 13 6143 :=
  good_of_checkR cert_13_6143 13 6143 (by decide +kernel)

/-- The cover of the class of `8193` modulo `2^14`. -/
def cert_14_8193 : RT :=
  (.beta (.node (.node (.node (.node .leaf .leaf) .leaf) .leaf) .leaf))

/-- The conclusion of the certificate holds for the class of `8193` modulo `2^14`. -/
theorem good_14_8193 : Good 14 8193 :=
  good_of_checkR cert_14_8193 14 8193 (by decide +kernel)

/-- The cover of the class of `16383` modulo `2^15`. -/
def cert_15_16383 : RT :=
  (.beta (.node .leaf (.node .leaf (.node .leaf .leaf))))

/-- The conclusion of the certificate holds for the class of `16383` modulo `2^15`. -/
theorem good_15_16383 : Good 15 16383 :=
  good_of_checkR cert_15_16383 15 16383 (by decide +kernel)

/-- The cover of the class of `32767` modulo `2^15`. -/
def cert_15_32767 : RT :=
  (.split (.split (.beta (.node .leaf (.node .leaf .leaf))) .none) (.split (.beta (.node .leaf
  (.node .leaf (.node .leaf .leaf)))) .none))

/-- The conclusion of the certificate holds for the class of `32767` modulo `2^15`. -/
theorem good_15_32767 : Good 15 32767 :=
  good_of_checkR cert_15_32767 15 32767 (by decide +kernel)

end TrTreeCertificate

end CollatzPosDens
