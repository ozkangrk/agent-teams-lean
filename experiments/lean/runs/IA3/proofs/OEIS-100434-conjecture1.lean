import FormalConjectures.OEIS.«100434»

/-! Swarm proof for OEIS A100434 conjecture1: c n + d n = b n. -/

namespace S100434

open Nat

theorem cd_core : ∀ m : ℕ,
    OeisA100434.c (2 * m) + OeisA100434.d (2 * m) = -OeisA100434.c (2 * m + 1) ∧
    OeisA100434.c (2 * m + 1) + OeisA100434.d (2 * m + 1) = OeisA100434.c (2 * m) := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
    constructor <;> rfl
  | one =>
    constructor <;> rfl
  | more k ih1 ih2 =>
    have hP1 := ih1.1
    have hQ1 := ih1.2
    have hP2' : OeisA100434.c (2 * k + 2) + OeisA100434.d (2 * k + 2)
        = -OeisA100434.c (2 * k + 3) := by
      rw [← show 2 * (k + 1) = 2 * k + 2 from by omega,
        ← show 2 * (k + 1) + 1 = 2 * k + 3 from by omega]
      exact ih2.1
    have hQ2' : OeisA100434.c (2 * k + 3) + OeisA100434.d (2 * k + 3)
        = OeisA100434.c (2 * k + 2) := by
      rw [← show 2 * (k + 1) + 1 = 2 * k + 3 from by omega,
        ← show 2 * (k + 1) = 2 * k + 2 from by omega]
      exact ih2.2
    refine ⟨?_, ?_⟩
    · rw [show 2 * (k + 2) + 1 = 2 * k + 5 from by omega,
        show 2 * (k + 2) = 2 * k + 4 from by omega]
      have rc4 : OeisA100434.c (2 * k + 4)
          = -6 * OeisA100434.c (2 * k + 2) - OeisA100434.c (2 * k) := rfl
      have rd4 : OeisA100434.d (2 * k + 4)
          = -6 * OeisA100434.d (2 * k + 2) - OeisA100434.d (2 * k) := rfl
      have rc5 : OeisA100434.c (2 * k + 5)
          = -6 * OeisA100434.c (2 * k + 3) - OeisA100434.c (2 * k + 1) := rfl
      rw [rc4, rd4, rc5]
      linarith
    · rw [show 2 * (k + 2) + 1 = 2 * k + 5 from by omega,
        show 2 * (k + 2) = 2 * k + 4 from by omega]
      have rc5 : OeisA100434.c (2 * k + 5)
          = -6 * OeisA100434.c (2 * k + 3) - OeisA100434.c (2 * k + 1) := rfl
      have rd5 : OeisA100434.d (2 * k + 5)
          = -6 * OeisA100434.d (2 * k + 3) - OeisA100434.d (2 * k + 1) := rfl
      have rc4 : OeisA100434.c (2 * k + 4)
          = -6 * OeisA100434.c (2 * k + 2) - OeisA100434.c (2 * k) := rfl
      rw [rc5, rd5, rc4]
      linarith

end S100434

theorem swarm_proof (n : ℕ) : OeisA100434.c n + OeisA100434.d n = OeisA100434.b n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [OeisA100434.b, if_pos (show (m + m) % 2 = 0 by omega),
      show m + m = 2 * m from by omega]
    exact (S100434.cd_core m).1
  · rw [OeisA100434.b, if_neg (show (2 * m + 1) % 2 ≠ 0 by omega)]
    exact (S100434.cd_core m).2
