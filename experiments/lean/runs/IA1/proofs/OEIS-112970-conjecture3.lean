import FormalConjectures.OEIS.«112970»

theorem swarm_proof : ∀ n : ℕ, OeisA112970.a (2^n - 1) = 1 := by
  have key : ∀ m : ℕ, 1 < m → m % 2 = 1 → OeisA112970.a m = OeisA112970.a (m / 2) := by
    intro m hm _
    rw [OeisA112970.a]
    split_ifs <;> first | omega | rfl
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact OeisA112970.a_0
  | one => exact OeisA112970.a_1
  | more k _ih1 ih2 =>
    have hp : 0 < 2 ^ k := by positivity
    have hpA : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ']
    rw [key (2 ^ (k + 2) - 1) (by omega) (by omega),
      show (2 ^ (k + 2) - 1) / 2 = 2 ^ (k + 1) - 1 by omega]
    exact ih2
