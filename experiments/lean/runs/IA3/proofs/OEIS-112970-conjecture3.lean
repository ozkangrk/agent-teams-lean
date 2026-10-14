import FormalConjectures.OEIS.«112970»

/-! Swarm proof for OEIS A112970 conjecture3: a (2^n - 1) = 1. -/

theorem swarm_proof : ∀ (n : ℕ), OeisA112970.a (2 ^ n - 1) = 1 := by
  intro n
  have key : ∀ m : ℕ, 3 ≤ m → m % 2 = 1 → OeisA112970.a m = OeisA112970.a (m / 2) := by
    intro m hm hmod
    rw [OeisA112970.a, if_neg (show m ≠ 0 by omega), if_neg (show m ≠ 1 by omega), if_pos hmod]
  induction n with
  | zero => rw [OeisA112970.a, if_pos (by decide)]
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      rw [OeisA112970.a, if_neg (by decide), if_pos (by decide)]
    · have hA : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hge : 4 ≤ 2 * 2 ^ n := by
        have h2n2 : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 1 ≤ n by omega)
        omega
      have hmod : (2 ^ (n + 1) - 1) % 2 = 1 := by omega
      have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by omega
      have hge3 : 3 ≤ 2 ^ (n + 1) - 1 := by omega
      rw [key (2 ^ (n + 1) - 1) hge3 hmod, hdiv]
      exact ih
