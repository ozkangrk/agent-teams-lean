import FormalConjectures.OEIS.«112970»

open OeisA112970

theorem a_odd_step (m : ℕ) (h1 : 1 < m) (hodd : m % 2 = 1) : a m = a (m / 2) := by
  conv_lhs => unfold a
  rw [if_neg (by omega), if_neg (by omega), if_pos hodd]

theorem swarm_proof (n : ℕ) : a (2^n) = a (2^(n + 1) + 1) := by
  have hpos : (0:ℕ) < 2^n := Nat.two_pow_pos n
  have hp : (2:ℕ)^(n+1) = 2 * (2:ℕ)^n := by rw [Nat.pow_succ]; ring
  rw [a_odd_step (2^(n+1)+1) (by rw [hp]; omega) (by rw [hp]; omega)]
  congr 1
  rw [hp]
  omega
