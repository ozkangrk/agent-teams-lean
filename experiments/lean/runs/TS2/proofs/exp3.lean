import FormalConjectures.OEIS.«112970»
example (x : ℕ) : 2 * x - 1 = 2 * (x - 1) + 1 := by omega
example (n : ℕ) : (2:ℕ)^(n+1) - 1 = 2 * ((2:ℕ)^n - 1) + 1 := by
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  rw [hp]
  omega
example (n : ℕ) : (2:ℕ)^(n+1) - 1 = 2 * ((2:ℕ)^n - 1) + 1 := by
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  rw [hp]
  trace_state
  sorry
