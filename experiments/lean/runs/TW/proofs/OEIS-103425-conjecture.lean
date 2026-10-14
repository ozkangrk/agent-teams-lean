import FormalConjectures.OEIS.«103425»

open OeisA103425

theorem swarm_proof : answer(True) ↔
    ∃ (a b c : ℤ) (x : ℕ → ℤ),
      Nat.gcd (Int.gcd a b) c.natAbs = 1 ∧
      IsWeightedTribonacci a b c x ∧
      ∀ n, ¬ (x n).natAbs.Prime := by
  constructor
  · intro _
    refine ⟨1, 1, -1, fun n ↦ 4 * (n + 1), by norm_num, fun n ↦ by push_cast; ring,
      fun n ↦ ?_⟩
    rw [show (4 * ((n : ℤ) + 1)).natAbs = 4 * (n + 1) by omega, Nat.prime_mul_iff]
    norm_num
  · intro _
    trivial
