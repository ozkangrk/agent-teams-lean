import FormalConjectures.OEIS.«100434»

open OeisA100434

theorem a_even2 : ∀ m : ℕ, a (2 * m) = -c (2 * m + 1) := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h_eq : 2 * (k + 2) = 2 * k + 4 := by omega
    have h_eq2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    rw [h_eq2, h_eq]
    have h_lhs : a (2 * k + 4) = -6 * a (2 * k + 2) - a (2 * k) := by rfl
    have h_rhs : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by rfl
    rw [h_lhs, h_rhs]
    have ih2' : a (2 * k + 2) = -c (2 * k + 3) := by
      have h_eq_ih : 2 * (k + 1) = 2 * k + 2 := by omega
      have h_eq2_ih : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [← h_eq2_ih, ← h_eq_ih]
      exact ih2
    rw [ih1, ih2']
    ring

theorem Q : ∀ m : ℕ, c (2 * m + 1) + d (2 * m + 1) = c (2 * m) := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    rw [show 2 * (k + 2) + 1 = 2 * k + 5 from by omega,
        show 2 * (k + 2) = 2 * k + 4 from by omega]
    have hc : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by rfl
    have hd : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := by rfl
    have hc4 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := by rfl
    have ih2' : c (2 * k + 3) + d (2 * k + 3) = c (2 * k + 2) := by
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by omega,
          show 2 * k + 2 = 2 * (k + 1) from by omega]
      exact ih2
    rw [hc, hd, hc4, ← ih2', ← ih1]
    ring

theorem a_odd2 (m : ℕ) : a (2 * m + 1) = d (2 * m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    rw [show 2 * (k + 2) + 1 = 2 * k + 5 from by omega]
    have h_lhs : a (2 * k + 5) = -6 * a (2 * k + 3) - a (2 * k + 1) := by rfl
    have h_rhs : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := by rfl
    rw [h_lhs, h_rhs]
    have ih2' : a (2 * k + 3) = d (2 * k + 3) := by
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by omega]
      exact ih2
    rw [ih1, ih2']

theorem swarm_proof (n : ℕ) : g n + a n = b n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m from by omega]
    rw [g, if_pos (by omega : (2 * m) % 2 = 0), a_even2, b,
      if_pos (by omega : (2 * m) % 2 = 0)]
    ring
  · rw [g, if_neg (by omega : ¬ ((2 * m + 1) % 2 = 0)), b,
      if_neg (by omega : ¬ ((2 * m + 1) % 2 = 0))]
    rw [show 2 * m + 1 - 1 = 2 * m from by omega]
    linarith [Q m, a_odd2 m]
