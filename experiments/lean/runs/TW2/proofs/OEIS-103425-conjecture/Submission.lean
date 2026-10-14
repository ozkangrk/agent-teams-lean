import FormalConjectures.OEIS.«103425»

open OeisA103425

theorem swarm_proof : answer(True) ↔
    ∃ (a b c : ℤ) (x : ℕ → ℤ),
      Nat.gcd (Int.gcd a b) c.natAbs = 1 ∧
      IsWeightedTribonacci a b c x ∧
      ∀ n, ¬ (x n).natAbs.Prime := by
  constructor
  · intro _
    obtain ⟨a, b, c, x, h1, h2, -, h4⟩ :=
      OeisA103425.conjecture.variants.nonconstant.mp trivial
    exact ⟨a, b, c, x, h1, h2, h4⟩
  · intro _
    trivial
