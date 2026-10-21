/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.StoppingTrace.TrTreeCertificateCover

/-!
# The gap-zero certificate, part 1 of 3

The covers of 15 residue classes, each checked by the kernel with
`CollatzPosDens.TrTreeCertificate.checkR` and turned into the conclusion
`CollatzPosDens.TrTreeCertificate.Good` of the certificate by
`CollatzPosDens.TrTreeCertificate.good_of_checkR`. The classes of all parts together, assembled in
`CollatzPosDens.trTreeCost_sub_trTailGain_lt`, cover every odd integer `m` with `0 < m < 2^16`.

## Main results

* `CollatzPosDens.TrTreeCertificate.good_3_3`, `good_4_9`, `good_6_31`, `good_7_65`, `good_8_129`,
  `good_8_241`, `good_9_257`, `good_10_399`, `good_10_513`, `good_11_113`, `good_13_2049`,
  `good_13_4097`, `good_13_6145`, `good_14_8191`, `good_16_32769`: the conclusion `Good k r` of the
  certificate for the residue class of `r` modulo `2^k`, for the classes of this part.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

namespace TrTreeCertificate

/-- The cover of the class of `3` modulo `2^3`. -/
def cert_3_3 : RT :=
  (.split (.beta .leaf) (.split (.beta .leaf) (.beta .leaf)))

/-- The conclusion of the certificate for the class of `3` modulo `2^3`. -/
theorem good_3_3 : Good 3 3 :=
  good_of_checkR cert_3_3 3 3 (by decide +kernel)

/-- The cover of the class of `9` modulo `2^4`. -/
def cert_4_9 : RT :=
  (.split (.split (.beta (.node .leaf .leaf)) (.beta (.node .leaf .leaf))) (.split (.beta .leaf)
  (.beta (.node .leaf .leaf))))

/-- The conclusion of the certificate for the class of `9` modulo `2^4`. -/
theorem good_4_9 : Good 4 9 :=
  good_of_checkR cert_4_9 4 9 (by decide +kernel)

/-- The cover of the class of `31` modulo `2^6`. -/
def cert_6_31 : RT :=
  (.split (.split (.beta (.node .leaf (.node .leaf .leaf))) (.beta (.node .leaf .leaf))) (.split
  (.beta (.node .leaf (.node .leaf .leaf))) (.beta (.node .leaf (.node .leaf .leaf)))))

/-- The conclusion of the certificate for the class of `31` modulo `2^6`. -/
theorem good_6_31 : Good 6 31 :=
  good_of_checkR cert_6_31 6 31 (by decide +kernel)

/-- The cover of the class of `65` modulo `2^7`. -/
def cert_7_65 : RT :=
  (.split (.split (.beta (.node (.node .leaf .leaf) .leaf)) (.beta (.node .leaf .leaf))) (.split
  (.beta .leaf) (.beta (.node .leaf .leaf))))

/-- The conclusion of the certificate for the class of `65` modulo `2^7`. -/
theorem good_7_65 : Good 7 65 :=
  good_of_checkR cert_7_65 7 65 (by decide +kernel)

/-- The cover of the class of `129` modulo `2^8`. -/
def cert_8_129 : RT :=
  (.split (.split (.beta (.node (.node .leaf .leaf) .leaf)) (.beta (.node (.node .leaf .leaf)
  .leaf))) (.split (.beta (.node .leaf .leaf)) (.beta (.node (.node .leaf .leaf) .leaf))))

/-- The conclusion of the certificate for the class of `129` modulo `2^8`. -/
theorem good_8_129 : Good 8 129 :=
  good_of_checkR cert_8_129 8 129 (by decide +kernel)

/-- The cover of the class of `241` modulo `2^8`. -/
def cert_8_241 : RT :=
  (.beta (.node .leaf .leaf))

/-- The conclusion of the certificate for the class of `241` modulo `2^8`. -/
theorem good_8_241 : Good 8 241 :=
  good_of_checkR cert_8_241 8 241 (by decide +kernel)

/-- The cover of the class of `257` modulo `2^9`. -/
def cert_9_257 : RT :=
  (.split (.beta (.node (.node (.node .leaf .leaf) .leaf) .leaf)) (.beta (.node (.node .leaf .leaf)
  .leaf)))

/-- The conclusion of the certificate for the class of `257` modulo `2^9`. -/
theorem good_9_257 : Good 9 257 :=
  good_of_checkR cert_9_257 9 257 (by decide +kernel)

/-- The cover of the class of `399` modulo `2^10`. -/
def cert_10_399 : RT :=
  (.beta (.node .leaf .leaf))

/-- The conclusion of the certificate for the class of `399` modulo `2^10`. -/
theorem good_10_399 : Good 10 399 :=
  good_of_checkR cert_10_399 10 399 (by decide +kernel)

/-- The cover of the class of `513` modulo `2^10`. -/
def cert_10_513 : RT :=
  (.split (.beta (.node (.node .leaf .leaf) .leaf)) (.beta (.node (.node .leaf .leaf) .leaf)))

/-- The conclusion of the certificate for the class of `513` modulo `2^10`. -/
theorem good_10_513 : Good 10 513 :=
  good_of_checkR cert_10_513 10 513 (by decide +kernel)

/-- The cover of the class of `113` modulo `2^11`. -/
def cert_11_113 : RT :=
  (.beta (.node .leaf .leaf))

/-- The conclusion of the certificate for the class of `113` modulo `2^11`. -/
theorem good_11_113 : Good 11 113 :=
  good_of_checkR cert_11_113 11 113 (by decide +kernel)

/-- The cover of the class of `2049` modulo `2^13`. -/
def cert_13_2049 : RT :=
  (.beta (.node (.node .leaf .leaf) .leaf))

/-- The conclusion of the certificate for the class of `2049` modulo `2^13`. -/
theorem good_13_2049 : Good 13 2049 :=
  good_of_checkR cert_13_2049 13 2049 (by decide +kernel)

/-- The cover of the class of `4097` modulo `2^13`. -/
def cert_13_4097 : RT :=
  (.beta (.node (.node (.node (.node .leaf .leaf) .leaf) .leaf) .leaf))

/-- The conclusion of the certificate for the class of `4097` modulo `2^13`. -/
theorem good_13_4097 : Good 13 4097 :=
  good_of_checkR cert_13_4097 13 4097 (by decide +kernel)

/-- The cover of the class of `6145` modulo `2^13`. -/
def cert_13_6145 : RT :=
  (.beta (.node (.node .leaf .leaf) .leaf))

/-- The conclusion of the certificate for the class of `6145` modulo `2^13`. -/
theorem good_13_6145 : Good 13 6145 :=
  good_of_checkR cert_13_6145 13 6145 (by decide +kernel)

/-- The cover of the class of `8191` modulo `2^14`. -/
def cert_14_8191 : RT :=
  (.beta (.node .leaf (.node .leaf (.node .leaf (.node .leaf .leaf)))))

/-- The conclusion of the certificate for the class of `8191` modulo `2^14`. -/
theorem good_14_8191 : Good 14 8191 :=
  good_of_checkR cert_14_8191 14 8191 (by decide +kernel)

/-- The cover of the class of `32769` modulo `2^16`. -/
def cert_16_32769 : RT :=
  (.split (.beta (.node (.node .leaf .leaf) .leaf)) .none)

/-- The conclusion of the certificate for the class of `32769` modulo `2^16`. -/
theorem good_16_32769 : Good 16 32769 :=
  good_of_checkR cert_16_32769 16 32769 (by decide +kernel)

end TrTreeCertificate

end CollatzPosDens
