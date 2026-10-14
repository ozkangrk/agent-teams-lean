import FormalConjectures.OEIS.«70823»

open OeisA70823

example : numDigitsBase10 243 = 3 := by decide
example : concatenate 243 72 = 24372 := by decide
example : a 8 % (13*13) = (0:Nat) := by decide
set_option maxRecDepth 10000 in
example : a 12 % (13*13) = (0:Nat) := by decide
