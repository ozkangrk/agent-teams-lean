
import FormalConjectures.OEIS.«3625»
open Polynomial ZMod

example : ¬ IsSquare (((3 : Nat) : ZMod 7)) := by decide
example : ¬ IsSquare (((5 : Nat) : ZMod 7)) := by norm_num; decide
example : IsSquare (((2 : Nat) : ZMod 7)) := by norm_num; decide
example : (((3 : Nat) : ZMod 7) = (3 : ZMod 7)) := by norm_num
