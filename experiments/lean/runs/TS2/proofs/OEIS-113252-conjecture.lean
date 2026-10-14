import FormalConjectures.OEIS.«113252»

open OeisA113252

def tz : ℕ → ℤ
  | 0 => 1
  | 1 => -2
  | (n+2) => -4 * tz (n+1) - 36 * tz n

def P : ℕ → ℚ := fun k =>
  (36 * (tz k : ℚ)^2 + 36 * (tz k : ℚ) * (tz (k+1) : ℚ) + (tz (k+1) : ℚ)^2) / 32

theorem key : ∀ k : ℕ, (a (2*k) : ℚ) = P k ∧ (a (2*k+1) : ℚ) = ((tz (k+1) : ℚ))^2 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => constructor <;> norm_num [P, tz, a]
    | 1 => constructor <;> norm_num [P, tz, a]
    | (k+2) =>
      have r1 : tz (k+2) = -4 * tz (k+1) - 36 * tz k := rfl
      have r3 : tz (k+3) = -20 * tz (k+1) + 144 * tz k := by
        rw [show tz (k+3) = -4 * tz (k+2) - 36 * tz (k+1) from rfl, r1]
        ring
      have c1 : (tz (k+2) : ℚ) = -4 * (tz (k+1) : ℚ) - 36 * (tz k : ℚ) := by
        rw [r1]; push_cast; ring
      have c3 : (tz (k+3) : ℚ) = -20 * (tz (k+1) : ℚ) + 144 * (tz k : ℚ) := by
        rw [r3]; push_cast; ring
      obtain ⟨he1, ho1⟩ := ih (k+1) (by omega)
      obtain ⟨he0, ho0⟩ := ih k (by omega)
      rw [show 2*(k+1) = 2*k+2 by omega] at he1
      rw [show 2*(k+1)+1 = 2*k+3 by omega, show k+1+1 = k+2 by omega] at ho1
      have hr4 : a (2*k+4) = -4 * a (2*k+3) + 144 * a (2*k+1) + 1296 * a (2*k) := rfl
      have hc4 := congrArg (Int.cast : ℤ → ℚ) hr4
      push_cast at hc4
      have heven : (a (2*k+4) : ℚ) = P (k+2) := by
        rw [hc4, ho1, ho0, he0]
        simp only [P]
        rw [show tz (k+2+1) = tz (k+3) from rfl, c1, c3]
        field_simp
        ring
      have hr5 : a (2*k+5) = -4 * a (2*k+4) + 144 * a (2*k+2) + 1296 * a (2*k+1) := rfl
      have hc5 := congrArg (Int.cast : ℤ → ℚ) hr5
      push_cast at hc5
      have hodd : (a (2*k+5) : ℚ) = ((tz (k+3) : ℚ))^2 := by
        rw [hc5, heven, he1, ho0]
        simp only [P]
        rw [show tz (k+2+1) = tz (k+3) from rfl, c1, c3]
        field_simp
        ring
      refine ⟨heven, ?_⟩
      rw [show 2 * (k+2) + 1 = 2 * k + 5 by omega, show tz (k+2+1) = tz (k+3) from rfl]
      exact hodd

theorem swarm_proof : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  obtain ⟨_, ho⟩ := key n
  have hz : a (2*n+1) = tz (n+1) * tz (n+1) := by
    have h2 : ((tz (n+1) : ℚ))^2 = (tz (n+1) * tz (n+1) : ℤ) := by push_cast; ring
    rw [h2] at ho
    exact Int.cast_injective ho
  exact ⟨tz (n+1), hz⟩
