import FormalConjectures.OEIS.«112970»

/-! Swarm proof for OEIS A112970 conjecture1. -/

theorem swarm_proof : ∀ (n : ℕ), OeisA112970.a (2 ^ n) = OeisA112970.a (2 ^ (n + 1) + 1) := by
  intro n
  have key : ∀ m : ℕ, 2 ≤ m → m % 2 = 1 → OeisA112970.a m = OeisA112970.a (m / 2) := by
    intro m hm hmod
    rw [OeisA112970.a, if_neg (show m ≠ 0 by omega), if_neg (show m ≠ 1 by omega), if_pos hmod]
  have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
  have hp := Nat.one_le_two_pow (n := n)
  have hge : 2 ≤ 2 ^ (n + 1) + 1 := by omega
  have hmod : (2 ^ (n + 1) + 1) % 2 = 1 := by omega
  have hdiv : (2 ^ (n + 1) + 1) / 2 = 2 ^ n := by omega
  rw [key (2 ^ (n + 1) + 1) hge hmod, hdiv]
