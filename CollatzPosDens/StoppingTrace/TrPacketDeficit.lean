/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrPacketValue

/-!
# The packet deficit

For integers `c, o`, the packet deficit is `δ^{pk}_{c,o} := F_{c,o}(0) / (c - 1)`, the packet
value at position `0` normalised by the packet length `c - 1`.

## Main definitions

* `CollatzPosDens.trPacketDeficit c o`: the packet deficit `δ^{pk}_{c,o}`.

## Main results

* `CollatzPosDens.sub_one_mul_trPacketDeficit`: for `c ≠ 1`,
  `(c - 1) δ^{pk}_{c,o} = F_{c,o}(0)`.

## Implementation notes

The definition is made for all natural numbers `c, o`, without the range restrictions
`3 ≤ c ≤ 16`, `1 ≤ o ≤ c` of [Mazur]; on that range it agrees with the definition there. It is
computable, so its values can be evaluated by the kernel.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The packet deficit `δ^{pk}_{c,o} := F_{c,o}(0) / (c - 1)`, where `F_{c,o}` is the packet
value `CollatzPosDens.trPacketValue`. -/
@[collatz_pos_dens "def_tr_packet_deficit"]
def trPacketDeficit (c o : ℕ) : ℚ :=
  trPacketValue c o 0 / ((c : ℚ) - 1)

/-- The packet deficit `δ^{pk}_{c,o}` equals `F_{c,o}(0) / (c - 1)`. -/
theorem trPacketDeficit_def (c o : ℕ) :
    trPacketDeficit c o = trPacketValue c o 0 / ((c : ℚ) - 1) := rfl

/-- For `c ≠ 1`, `(c - 1) δ^{pk}_{c,o} = F_{c,o}(0)`. -/
theorem sub_one_mul_trPacketDeficit {c : ℕ} (hc : c ≠ 1) (o : ℕ) :
    ((c : ℚ) - 1) * trPacketDeficit c o = trPacketValue c o 0 := by
  have : (c : ℚ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hc)
  rw [trPacketDeficit, mul_div_cancel₀ _ this]

example : trPacketDeficit 3 1 = 1 / 2 := by
  rw [trPacketDeficit, trPacketValue_eq_pvN, show pvN 3 1 = 10 ^ 6 by decide +kernel]
  norm_num

end CollatzPosDens
