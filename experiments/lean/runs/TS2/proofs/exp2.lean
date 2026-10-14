import FormalConjectures.OEIS.«112970»
example (n : ℕ) : (2:ℕ)^(n+1) - 1 = 2 * ((2:ℕ)^n - 1) + 1 := by
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  omega

example (n : ℕ) (h : 0 < (2:ℕ)^n) : (2:ℕ)^(n+1) - 1 = 2 * ((2:ℕ)^n - 1) + 1 := by
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  omega
