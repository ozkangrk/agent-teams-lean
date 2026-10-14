
import FormalConjectures.OEIS.«3625»

open OeisA3625 Polynomial ZMod legendreSym

namespace A3625Aux

#check @neg_one_sq
example : (2 : ZMod 2) = 0 := by decide
example : IsRoot (X ^ 2 + X + 2 : (ZMod 2)[X]) 0 := by decide
example : IsRoot (X ^ 2 + X + 2 : (ZMod 7)[X]) 3 := by decide
example (x : ZMod 7) : eval x (X ^ 2 + X + 2) = x ^ 2 + x + 2 := by simp

end A3625Aux
