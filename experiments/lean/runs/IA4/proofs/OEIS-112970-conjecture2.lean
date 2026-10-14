import FormalConjectures.OEIS.«112970»

open OeisA112970

theorem odd_step (m : ℕ) (hm : 1 ≤ m) : a (2 * m + 1) = a m := by
  have h0 : ¬(2 * m + 1 = 0) := by omega
  have h1 : ¬(2 * m + 1 = 1) := by omega
  have hmod : (2 * m + 1) % 2 = 1 := by omega
  rw [a.eq_def, if_neg h0, if_neg h1, if_pos hmod]
  show a ((2 * m + 1) / 2) = a m
  congr 1
  omega

theorem swarm_proof (n : ℕ) : a (2^n - 1) = a (3 * 2^n - 1) := by
  induction n with
  | zero =>
    show a (2^0 - 1) = a (3 * 2^0 - 1)
    rw [a.eq_def, if_pos (show 2 ^ 0 - 1 = 0 by decide)]
    rw [a.eq_def,
      if_neg (show ¬(3 * 2 ^ 0 - 1 = 0) by decide),
      if_neg (show ¬(3 * 2 ^ 0 - 1 = 1) by decide),
      if_neg (show ¬((3 * 2 ^ 0 - 1) % 2 = 1) by decide)]
    show 1 = a ((3 * 2 ^ 0 - 1) / 2) + (if (3 * 2 ^ 0 - 1) / 2 < 2 then 0 else a ((3 * 2 ^ 0 - 1) / 2 - 2))
    rw [if_pos (show (3 * 2 ^ 0 - 1) / 2 < 2 by decide), Nat.add_zero, a.eq_def,
      if_neg (show ¬((3 * 2 ^ 0 - 1) / 2 = 0) by decide),
      if_pos (show (3 * 2 ^ 0 - 1) / 2 = 1 by decide)]
  | succ n ih =>
    cases n with
    | zero =>
      show a 1 = a 5
      rw [a.eq_def, if_neg (show ¬(1 = 0) by decide), if_pos rfl]
      rw [a.eq_def,
        if_neg (show ¬(5 = 0) by decide),
        if_neg (show ¬(5 = 1) by decide),
        if_pos (show 5 % 2 = 1 by decide)]
      show 1 = a (5 / 2)
      rw [a.eq_def,
        if_neg (show ¬(5 / 2 = 0) by decide),
        if_neg (show ¬(5 / 2 = 1) by decide),
        if_neg (show ¬(5 / 2 % 2 = 1) by decide)]
      show 1 = a (5 / 2 / 2) + (if 5 / 2 / 2 < 2 then 0 else a (5 / 2 / 2 - 2))
      rw [if_pos (show 5 / 2 / 2 < 2 by decide), Nat.add_zero, a.eq_def,
        if_neg (show ¬(5 / 2 / 2 = 0) by decide),
        if_pos (show 5 / 2 / 2 = 1 by decide)]
    | succ k =>
      have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : 2 ≤ 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      have hp : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring
      have key1 : 2 * 2 ^ (k + 1) - 1 = 2 * (2 ^ (k + 1) - 1) + 1 := by omega
      have key2 : 3 * (2 * 2 ^ (k + 1)) - 1 = 2 * (3 * 2 ^ (k + 1) - 1) + 1 := by omega
      have hm1 : 1 ≤ 2 ^ (k + 1) - 1 := by omega
      have hm2 : 1 ≤ 3 * 2 ^ (k + 1) - 1 := by omega
      rw [hp, key1, odd_step _ hm1, key2, odd_step _ hm2]
      exact ih
