import FormalConjectures.OEIS.«112970»

theorem swarm_proof : ∀ (n : ℕ), OeisA112970.a (2 ^ n - 1) = OeisA112970.a (3 * 2 ^ n - 1) := by
  have key : ∀ m : ℕ, OeisA112970.a (2 * m + 1) = OeisA112970.a m := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp [OeisA112970.a]
    · have h1 : 2 * m + 1 ≠ 0 := by omega
      have h2 : 2 * m + 1 ≠ 1 := by omega
      have h3 : (2 * m + 1) % 2 = 1 := by omega
      have h4 : (2 * m + 1) / 2 = m := by omega
      rw [OeisA112970.a, if_neg h1, if_neg h2, if_pos h3, h4]
  have L1 : ∀ n : ℕ, OeisA112970.a (2 ^ n - 1) = 1 := by
    intro n
    induction n with
    | zero => simp [OeisA112970.a]
    | succ n ih =>
      have hpos : 0 < 2 ^ n := by positivity
      rw [show 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 by rw [pow_succ]; omega]
      rw [key, ih]
  have L2 : ∀ n : ℕ, OeisA112970.a (3 * 2 ^ n - 1) = 1 := by
    intro n
    induction n with
    | zero => simp [OeisA112970.a]
    | succ n ih =>
      have hpos : 0 < 2 ^ n := by positivity
      rw [show 3 * 2 ^ (n + 1) - 1 = 2 * (3 * 2 ^ n - 1) + 1 by rw [pow_succ]; omega]
      rw [key, ih]
  intro n
  rw [L1 n, L2 n]
