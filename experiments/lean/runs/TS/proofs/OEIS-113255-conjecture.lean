import FormalConjectures.OEIS.«113255»

open OeisA113255

theorem Q : ∀ m : ℕ,
    2 * a (2 * m + 3) = 6561 * a (2 * m) + 162 * a (2 * m + 1) + 73 * a (2 * m + 2) ∧
    a (2 * m + 4) = -6561 * a (2 * m) - 146 * a (2 * m + 2) ∧
    a (2 * m + 5) = 26244 * a (2 * m) + 6561 * a (2 * m + 1) + 908 * a (2 * m + 2) := by
  intro m
  induction m with
  | zero => norm_num [a]
  | succ m ih =>
    obtain ⟨R1, R2, R3⟩ := ih
    ring_nf at R1 R2 R3 ⊢
    have d6 : a (2 * m + 6) = -4 * a (2 * m + 5) + 324 * a (2 * m + 3) + 6561 * a (2 * m + 2) := by
      have : a ((2 * m + 2) + 4) = -4 * a ((2 * m + 2) + 3) + 324 * a ((2 * m + 2) + 1)
          + 6561 * a (2 * m + 2) := rfl
      simpa using this
    have d7 : a (2 * m + 7) = -4 * a (2 * m + 6) + 324 * a (2 * m + 4) + 6561 * a (2 * m + 3) := by
      have : a ((2 * m + 3) + 4) = -4 * a ((2 * m + 3) + 3) + 324 * a ((2 * m + 3) + 1)
          + 6561 * a (2 * m + 3) := rfl
      simpa using this
    ring_nf at d6 d7
    constructor
    · linarith
    · constructor
      · linarith
      · linarith

theorem A : ∀ m : ℕ, a (2 * m + 7) = -65 * a (2 * m + 5) + 5265 * a (2 * m + 3)
    + 531441 * a (2 * m + 1) := by
  intro m
  obtain ⟨R1, R2, R3⟩ := Q (m + 1)
  obtain ⟨R1', R2', R3'⟩ := Q m
  ring_nf at R1 R2 R3 R1' R2' R3' ⊢
  linarith

def b : ℕ → ℤ
  | 0 => 2
  | 1 => 73
  | (m + 2) => -4 * b (m + 1) - 81 * b m

theorem T : ∀ m : ℕ, a (2 * m + 1) = b m * b m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rcases m with _ | _ | _ | _ | k
    · norm_num [a, b]
    · norm_num [a, b]
    · norm_num [a, b]
    · norm_num [a, b]
    · rw [show 2 * (k + 1 + 3) + 1 = 2 * (k + 1) + 7 from by omega, A (k + 1)]
      have h1 := ih (k + 1) (by omega)
      have h2 := ih (k + 1 + 1) (by omega)
      have h3 := ih (k + 1 + 2) (by omega)
      rw [show 2 * (k + 1 + 2) + 1 = 2 * (k + 1) + 5 from by omega] at h3
      rw [show 2 * (k + 1 + 1) + 1 = 2 * (k + 1) + 3 from by omega] at h2
      rw [h3, h2, h1]
      simp only [b]
      ring

theorem swarm_proof : ∀ (n : ℕ), IsSquare (a (2 * n + 1)) := by
  intro n
  exact ⟨b n, T n⟩
