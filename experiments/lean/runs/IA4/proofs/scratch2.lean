import FormalConjectures.OEIS.«112970»
open OeisA112970

example (k : ℕ) : 2 * 2 ^ (k + 1) - 1 = 2 * (2 ^ (k + 1) - 1) + 1 := by omega

example (k : ℕ) (h2 : 2 ≤ 2 ^ (k + 1)) : 2 * 2 ^ (k + 1) - 1 = 2 * (2 ^ (k + 1) - 1) + 1 := by omega

example (k : ℕ) : 2 * (2 ^ k * 2) - 1 = 2 * (2 ^ k * 2 - 1) + 1 := by omega

example (k : ℕ) : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring

example (k : ℕ) (h2 : 2 ≤ 2 ^ (k + 1)) : 1 ≤ 2 ^ (k + 1) - 1 := by omega
