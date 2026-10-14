import FormalConjectures.OEIS.«112970»

open OeisA112970

theorem two_pow_pos (n : ℕ) : 1 ≤ 2 ^ n := Nat.one_le_two_pow

example (n : ℕ) : 1 ≤ 2 ^ n - 1 := by
  have := two_pow_pos n
  omega

theorem odd_step (m : ℕ) (hm : 1 ≤ m) : a (2 * m + 1) = a m := by
  rw [a.eq_def,
    if_neg (show ¬(2 * m + 1 = 0) by omega),
    if_neg (show ¬(2 * m + 1 = 1) by omega),
    if_pos (show (2 * m + 1) % 2 = 1 by omega)]
  show a ((2 * m + 1) / 2) = a m
  congr 1
  omega

example (n : ℕ) : a (2^n - 1) = 1 := by
  induction n with
  | zero => show a (1 - 1) = 1; rw [a.eq_def, if_pos rfl]
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
    rw [hp]
    rw [show 2 * 2 ^ n - 1 = 2 * (2 ^ n - 1) + 1 by omega]
    rw [odd_step (2 ^ n - 1) (by have := two_pow_pos n; omega)]
    exact ih
