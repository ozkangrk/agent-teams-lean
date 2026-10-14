import FormalConjectures.OEIS.«113255»

/-! Swarm proof for OEIS A113255: a(2n+1) is always a square. -/

namespace S113255

open OeisA113255

theorem a_rec (n : ℕ) : a (n + 4) = -4 * a (n + 3) + 324 * a (n + 1) + 6561 * a n := rfl

/-- Roots of the square subsequence. -/
def u : ℕ → ℤ
| 0 => 2
| 1 => 73
| n + 2 => -4 * u (n + 1) - 81 * u n

theorem u_rec2 : ∀ n : ℕ, u (n + 2) + 4 * u (n + 1) + 81 * u n = 0 := by
  intro n
  have h : u (n + 2) = -4 * u (n + 1) - 81 * u n := rfl
  linarith

theorem u_sq_rec : ∀ n : ℕ,
    u (n + 3) ^ 2 = -65 * u (n + 2) ^ 2 + 5265 * u (n + 1) ^ 2 + 531441 * u n ^ 2 := by
  intro n
  have h3 : u (n + 3) = -4 * u (n + 2) - 81 * u (n + 1) := rfl
  have hf : (u (n + 2) + 4 * u (n + 1) + 81 * u n) * (u (n + 2) + 4 * u (n + 1) - 81 * u n) = 0 := by
    rw [u_rec2 n]; ring
  rw [h3]
  nlinarith [hf]

theorem c_rec : ∀ n : ℕ,
    a (2 * n + 7) = -65 * a (2 * n + 5) + 5265 * a (2 * n + 3) + 531441 * a (2 * n + 1) := by
  intro n
  have e1 := a_rec (2 * n + 3)
  have e2 := a_rec (2 * n + 2)
  have e3 := a_rec (2 * n + 1)
  linarith

theorem main : ∀ n : ℕ, a (2 * n + 1) = u n ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n <;> rfl
    · have hc := c_rec (n - 3)
      rw [show 2 * (n - 3) + 7 = 2 * n + 1 from by omega,
        show 2 * (n - 3) + 5 = 2 * (n - 1) + 1 from by omega,
        show 2 * (n - 3) + 3 = 2 * (n - 2) + 1 from by omega] at hc
      have h1 : a (2 * (n - 1) + 1) = u (n - 1) ^ 2 := ih (n - 1) (by omega)
      have h2 : a (2 * (n - 2) + 1) = u (n - 2) ^ 2 := ih (n - 2) (by omega)
      have h4 : a (2 * (n - 3) + 1) = u (n - 3) ^ 2 := ih (n - 3) (by omega)
      have hu := u_sq_rec (n - 3)
      rw [show n - 3 + 3 = n from by omega, show n - 3 + 2 = n - 1 from by omega,
        show n - 3 + 1 = n - 2 from by omega] at hu
      rw [hc, h1, h2, h4]
      linarith

end S113255

theorem swarm_proof : ∀ (n : ℕ), IsSquare (OeisA113255.a (2 * n + 1)) := by
  intro n
  exact ⟨S113255.u n, by rw [S113255.main n, pow_two]⟩
