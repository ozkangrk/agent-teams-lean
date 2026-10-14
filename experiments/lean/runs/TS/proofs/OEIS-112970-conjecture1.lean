import FormalConjectures.OEIS.«112970»

theorem swarm_proof : ∀ (n : ℕ), OeisA112970.a (2 ^ n) = OeisA112970.a (2 ^ (n + 1) + 1) := by
  intro n
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
  rw [show 2 ^ (n + 1) + 1 = 2 * 2 ^ n + 1 by rw [pow_succ]; omega]
  exact (key (2 ^ n)).symm
