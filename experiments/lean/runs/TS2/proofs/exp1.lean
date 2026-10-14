import FormalConjectures.OEIS.«112970»

example (n : ℕ) : (2:ℕ)^(n+1) + 1 ≡ 1 [MOD 2] := by
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  omega

example (n : ℕ) : ((2:ℕ)^(n+1) + 1) % 2 = 1 := by
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  rw [hp]
  omega

example (n : ℕ) : ((2:ℕ)^(n+1) + 1) % 2 = 1 := by
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  omega
