import FormalConjectures.OEIS.«112970»

open OeisA112970

theorem swarm_proof (n : ℕ) : a (2^n) = a (2^(n + 1) + 1) := by
  have key : ∀ k : ℕ, 1 ≤ k → a (2 * k + 1) = a k := by
    intro k hk
    conv_lhs => unfold a
    rw [if_neg (by omega : (2 * k + 1) ≠ 0), if_neg (by omega : (2 * k + 1) ≠ 1),
      if_pos (show (2 * k + 1) % 2 = 1 by omega)]
    rw [show (2 * k + 1) / 2 = k by omega]
  rw [show 2 ^ (n + 1) + 1 = 2 * 2 ^ n + 1 from by rw [pow_succ]; ring]
  exact (key (2 ^ n) Nat.one_le_two_pow).symm
