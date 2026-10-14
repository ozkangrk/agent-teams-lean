import FormalConjectures.OEIS.«112970»

namespace OeisA112970

example (m : ℕ) (hm : 1 < m) (hodd : m % 2 = 1) : a m = a (m / 2) := by
  rw [a]
  split_ifs <;> first | omega | rfl

example : a (2 ^ 0 - 1) = 1 := a_0

example : a (3 * 2 ^ 0 - 1) = 1 := a_2

end OeisA112970
