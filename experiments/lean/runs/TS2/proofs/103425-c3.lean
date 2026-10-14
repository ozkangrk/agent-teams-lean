import FormalConjectures.OEIS.«103425»

/-! OEIS-103425 conjecture (A103425): a constant-composite weighted tribonacci witness. -/

open OeisA103425

theorem swarm_proof : answer(True) ↔
    ∃ (a b c : ℤ) (x : ℕ → ℤ),
      Nat.gcd (Int.gcd a b) c.natAbs = 1 ∧
      IsWeightedTribonacci a b c x ∧
      ∀ n, ¬ (x n).natAbs.Prime := by
  constructor
  · intro _
    refine ⟨1, 1, -1, fun _ ↦ 4, by norm_num, fun n ↦ by norm_num, fun n ↦ by norm_num⟩
  · intro _
    trivial
