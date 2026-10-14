import FormalConjectures.OEIS.«112970»

open OeisA112970

theorem swarm_proof (n : ℕ) : a (2^n - 1) = a (3 * 2^n - 1) := by
  have key : ∀ k : ℕ, a (2 * k + 1) = a k := by
    intro k
    match k with
    | 0 => simp [a]
    | k + 1 =>
      conv_lhs => unfold a
      rw [if_neg (by omega : (2 * (k + 1) + 1) ≠ 0), if_neg (by omega : (2 * (k + 1) + 1) ≠ 1),
        if_pos (show (2 * (k + 1) + 1) % 2 = 1 by omega)]
      rw [show (2 * (k + 1) + 1) / 2 = k + 1 by omega]
  have h1 : ∀ n : ℕ, a (2 ^ n - 1) = 1 := by
    intro n
    induction n with
    | zero => simp [a]
    | succ n ih =>
      have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [show 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 from by rw [pow_succ]; omega]
      exact key (2 ^ n - 1) ▸ ih
  have h2 : ∀ n : ℕ, a (3 * 2 ^ n - 1) = 1 := by
    intro n
    induction n with
    | zero => simp [a]
    | succ n ih =>
      have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [show 3 * 2 ^ (n + 1) - 1 = 2 * (3 * 2 ^ n - 1) + 1 from by rw [pow_succ]; omega]
      exact key (3 * 2 ^ n - 1) ▸ ih
  rw [h1 n, h2 n]
