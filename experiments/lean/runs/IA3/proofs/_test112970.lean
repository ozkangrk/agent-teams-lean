import FormalConjectures.OEIS.«112970»

example : (2 : ℕ) ^ 0 - 1 = 0 := rfl

example : OeisA112970.a 0 = 1 := rfl

example : OeisA112970.a 2 = 1 := rfl

example : OeisA112970.a (2 ^ 0 - 1) = 1 := by
  show OeisA112970.a 0 = 1
  rfl

example : OeisA112970.a (3 * 2 ^ 0 - 1) = 1 := by
  show OeisA112970.a 2 = 1
  rfl

example (n : ℕ) : 1 ≤ 2 ^ n := Nat.one_le_two_pow
