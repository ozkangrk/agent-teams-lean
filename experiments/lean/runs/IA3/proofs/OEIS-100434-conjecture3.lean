import FormalConjectures.OEIS.«100434»

/-! Swarm proof for OEIS A100434 conjecture3. -/

namespace S100434C3

open OeisA100434

theorem key_odd : ∀ k : ℕ, c (2 * k + 1) + d (2 * k + 1) = c (2 * k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h_eq2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have h_eq : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [h_eq2, h_eq]
    have hc1 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := rfl
    have hd1 : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := rfl
    have hc2 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := rfl
    rw [hc1, hd1, hc2]
    have ih2' : c (2 * k + 3) + d (2 * k + 3) = c (2 * k + 2) := by
      have h_eq_ih : 2 * (k + 1) = 2 * k + 2 := by omega
      have h_eq2_ih : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [← h_eq2_ih, ← h_eq_ih]
      exact ih2
    linarith [ih1, ih2']

theorem main : ∀ (n : ℕ), g n + a n = b n := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k from by omega]
    have hmod : (2 * k) % 2 = 0 := by omega
    rw [g, if_pos hmod, b, if_pos hmod, OeisA100434.a_even]
    omega
  · subst hk
    have hne : (2 * k + 1) % 2 ≠ 0 := by omega
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [g, if_neg hne, b, if_neg hne, hsub, OeisA100434.a_odd]
    exact key_odd k

end S100434C3

theorem swarm_proof : ∀ (n : ℕ), OeisA100434.g n + OeisA100434.a n = OeisA100434.b n :=
  S100434C3.main
