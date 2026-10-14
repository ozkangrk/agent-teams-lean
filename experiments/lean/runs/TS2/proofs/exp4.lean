import FormalConjectures.OEIS.«112970»
example (x : ℕ) (h : 1 ≤ x) : 2 * x - 1 = 2 * (x - 1) + 1 := by omega
example (n : ℕ) (hpos : 0 < (2:ℕ)^n) : (2:ℕ)^(n+1) - 1 = 2 * ((2:ℕ)^n - 1) + 1 := by
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  omega
