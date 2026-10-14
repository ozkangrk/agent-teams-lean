
import FormalConjectures.OEIS.«3625»
open Polynomial ZMod
variable {p : Nat} [Fact p.Prime]

example : ((2 : ZMod p) : (ZMod p)[X]) = C (2 : ZMod p) := rfl
example : (X + 2 : (ZMod p)[X]) = X + C (2 : ZMod p) := rfl
example : (X ^ 2 + X + 2 : (ZMod p)[X]) = X ^ 2 + (X + C (2 : ZMod p)) := by rw [add_assoc]; rfl
example : (X ^ 2 + X + 2 : (ZMod p)[X]).natDegree = 2 := by
  rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow 2
  · exact natDegree_X_add_C _
