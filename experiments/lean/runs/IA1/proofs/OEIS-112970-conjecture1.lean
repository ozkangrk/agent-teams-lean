import FormalConjectures.OEIS.«112970»

theorem swarm_proof : ∀ n : ℕ, OeisA112970.a (2^n) = OeisA112970.a (2^(n + 1) + 1) := by
  have key : ∀ m : ℕ, 1 < m → m % 2 = 1 → OeisA112970.a m = OeisA112970.a (m / 2) := by
    intro m hm _
    rw [OeisA112970.a]
    split_ifs <;> first | omega | rfl
  intro n
  have hp : 0 < 2 ^ n := by positivity
  have hpA : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ']
  rw [key (2 ^ (n + 1) + 1) (by omega) (by omega),
    show (2 ^ (n + 1) + 1) / 2 = 2 ^ n by omega]
