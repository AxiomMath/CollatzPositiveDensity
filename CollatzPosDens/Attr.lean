module

public meta import Lean

/-!
# The `collatz_pos_dens` tag attribute

This file declares the attribute `collatz_pos_dens`, which takes a string literal naming a tag
and attaches that tag to the declaration it marks. The attribute stores nothing in the
environment.
-/

public meta section

open Lean

/-- The attribute attaching a tag, given as a string literal, to a declaration. -/
syntax (name := collatz_pos_dens) "collatz_pos_dens " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `collatz_pos_dens
  descr := "marks a declaration as formalizing a blueprint entity"
  add   := fun _ _ _ => pure ()
}

end
