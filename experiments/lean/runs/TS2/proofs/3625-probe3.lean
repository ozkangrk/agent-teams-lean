
example : ¬ IsSquare (((3 : Nat) : ZMod 7)) := by decide
example : ¬ IsSquare (((5 : Nat) : ZMod 7)) := by norm_num; decide
example : IsSquare (((2 : Nat) : ZMod 7)) := by norm_num; decide
