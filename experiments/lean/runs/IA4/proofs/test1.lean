import FormalConjectures.OEIS.«112970»

open OeisA112970

example : a (2^3) = a (2^4 + 1) := by
  norm_num [a, Nat.div_add_mod]

example : a 20 % (13*13) = (0:Nat) := by decide
