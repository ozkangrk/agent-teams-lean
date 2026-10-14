import FormalConjectures.OEIS.«112970»

open OeisA112970

theorem odd_step (m : ℕ) (hm : 1 ≤ m) : a (2 * m + 1) = a m := by
  rw [a.eq_def,
    if_neg (show ¬(2 * m + 1 = 0) by omega),
    if_neg (show ¬(2 * m + 1 = 1) by omega),
    if_pos (show (2 * m + 1) % 2 = 1 by omega)]
  show a ((2 * m + 1) / 2) = a m
  congr 1
  omega

theorem swarm_proof (n : ℕ) : a (2^n) = a (2^(n + 1) + 1) := by
  have key := odd_step (2 ^ n) (Nat.one_le_two_pow)
  rw [show 2^(n+1) + 1 = 2 * 2^n + 1 by rw [Nat.pow_succ]; ring]
  rw [key]
