import FormalConjectures.OEIS.«113250»

open OeisA113250

theorem Q : ∀ m : ℕ,
    a (2 * m + 3) = 128 * a (2 * m) + 16 * a (2 * m + 1) + 4 * a (2 * m + 2) ∧
    a (2 * m + 4) = -256 * a (2 * m) - 16 * a (2 * m + 2) ∧
    a (2 * m + 5) = 1024 * a (2 * m) + 256 * a (2 * m + 1) + 128 * a (2 * m + 2) := by
  intro m
  induction m with
  | zero => norm_num [a]
  | succ m ih =>
    obtain ⟨R1, R2, R3⟩ := ih
    ring_nf at R1 R2 R3 ⊢
    have d6 : a (2 * m + 6) = -4 * a (2 * m + 5) + 64 * a (2 * m + 3) + 256 * a (2 * m + 2) := by
      have : a ((2 * m + 2) + 4) = -4 * a ((2 * m + 2) + 3) + 64 * a ((2 * m + 2) + 1)
          + 256 * a (2 * m + 2) := rfl
      simpa using this
    have d7 : a (2 * m + 7) = -4 * a (2 * m + 6) + 64 * a (2 * m + 4) + 256 * a (2 * m + 3) := by
      have : a ((2 * m + 3) + 4) = -4 * a ((2 * m + 3) + 3) + 64 * a ((2 * m + 3) + 1)
          + 256 * a (2 * m + 3) := rfl
      simpa using this
    ring_nf at d6 d7
    constructor
    · linarith
    · constructor
      · linarith
      · linarith

theorem A : ∀ m : ℕ, a (2 * m + 7) = 4096 * a (2 * m + 1) := by
  intro m
  obtain ⟨R1, R2, R3⟩ := Q (m + 1)
  obtain ⟨R1', R2', R3'⟩ := Q m
  ring_nf at R1 R2 R3 R1' R2' R3' ⊢
  linarith

def b : ℕ → ℤ
  | 0 => 2
  | 1 => 8
  | 2 => -64
  | (m + 3) => 64 * b m

theorem T : ∀ m : ℕ, a (2 * m + 1) = b m * b m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rcases m with _ | _ | _ | _ | k
    · rfl
    · rfl
    · rfl
    · norm_num [a, b]
    · rw [show 2 * (k + 1 + 3) + 1 = 2 * (k + 1) + 7 from by omega, A (k + 1), b]
      have hih := ih (k + 1) (by omega)
      rw [hih]
      ring

theorem swarm_proof : ∀ (n : ℕ), IsSquare (a (2 * n + 1)) := by
  intro n
  exact ⟨b n, T n⟩
