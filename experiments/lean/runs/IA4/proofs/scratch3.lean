import FormalConjectures.OEIS.«100434»
open OeisA100434
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
