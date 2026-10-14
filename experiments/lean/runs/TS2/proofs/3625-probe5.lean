
import FormalConjectures.OEIS.«3625»
open Polynomial ZMod

example : (IsSquare (((3 : Nat) : ZMod 7)) ↔ (3 = 1 ∨ 3 = 2 ∨ 3 = 4)) := by decide
example : ¬ (IsSquare (((3 : Nat) : ZMod 7))) := by decide
