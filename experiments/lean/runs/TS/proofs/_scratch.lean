import FormalConjectures.OEIS.«112970»

example (m : ℕ) : (2 * m + 1) / 2 = m := by omega
example (m : ℕ) : (2 * m + 1) % 2 = 1 := by omega
example (m : ℕ) : (m * 2 + 1) / 2 = m := by simp [Nat.mul_add_div]
