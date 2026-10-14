import FormalConjectures.OEIS.«100434»

private theorem heven : ∀ n : ℕ, 2 ∣ OeisA100434.d n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨-5, rfl⟩
      · exact ⟨-12, rfl⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      obtain ⟨x, hx⟩ := ih (m + 2) (by omega)
      obtain ⟨y, hy⟩ := ih m (by omega)
      refine ⟨-6 * x - y, ?_⟩
      have u : OeisA100434.d (m + 4) = -6 * OeisA100434.d (m + 2) - OeisA100434.d m := by rfl
      rw [u, hx, hy]
      ring

private theorem Bl : ∀ k : ℕ, OeisA100434.c (2 * k + 1) + OeisA100434.d (2 * k + 1)
    = OeisA100434.c (2 * k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have ih2' : OeisA100434.c (2 * k + 3) + OeisA100434.d (2 * k + 3)
        = OeisA100434.c (2 * k + 2) := by
      have := ih2
      rw [show (2:ℕ)*(k+1)+1 = 2*k+3 by omega] at this
      rw [show (2:ℕ)*(k+1) = 2*k+2 by omega] at this
      exact this
    rw [show (2:ℕ)*(k+2)+1 = 2*k+5 by omega, show (2:ℕ)*(k+2) = 2*k+4 by omega]
    have u1 : OeisA100434.c (2*k+5) = -6 * OeisA100434.c (2*k+3) - OeisA100434.c (2*k+1) := by rfl
    have u2 : OeisA100434.d (2*k+5) = -6 * OeisA100434.d (2*k+3) - OeisA100434.d (2*k+1) := by rfl
    have u3 : OeisA100434.c (2*k+4) = -6 * OeisA100434.c (2*k+2) - OeisA100434.c (2*k) := by rfl
    rw [u1, u2, u3]
    linarith

private theorem Cl : ∀ k : ℕ, OeisA100434.d (2 * k) + OeisA100434.d (2 * k + 1)
    = -2 * OeisA100434.c (2 * k + 1) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have ih2' : OeisA100434.d (2 * k + 2) + OeisA100434.d (2 * k + 3)
        = -2 * OeisA100434.c (2 * k + 3) := by
      have := ih2
      rw [show (2:ℕ)*(k+1)+1 = 2*k+3 by omega] at this
      rw [show (2:ℕ)*(k+1) = 2*k+2 by omega] at this
      exact this
    rw [show (2:ℕ)*(k+2)+1 = 2*k+5 by omega, show (2:ℕ)*(k+2) = 2*k+4 by omega]
    have u1 : OeisA100434.d (2*k+4) = -6 * OeisA100434.d (2*k+2) - OeisA100434.d (2*k) := by rfl
    have u2 : OeisA100434.d (2*k+5) = -6 * OeisA100434.d (2*k+3) - OeisA100434.d (2*k+1) := by rfl
    have u3 : OeisA100434.c (2*k+5) = -6 * OeisA100434.c (2*k+3) - OeisA100434.c (2*k+1) := by rfl
    rw [u1, u2, u3]
    linarith

private theorem Dl : ∀ k : ℕ, OeisA100434.d (2 * k + 1) - OeisA100434.d (2 * k)
    = 2 * OeisA100434.c (2 * k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have ih2' : OeisA100434.d (2 * k + 3) - OeisA100434.d (2 * k + 2)
        = 2 * OeisA100434.c (2 * k + 2) := by
      have := ih2
      rw [show (2:ℕ)*(k+1)+1 = 2*k+3 by omega] at this
      rw [show (2:ℕ)*(k+1) = 2*k+2 by omega] at this
      exact this
    rw [show (2:ℕ)*(k+2)+1 = 2*k+5 by omega, show (2:ℕ)*(k+2) = 2*k+4 by omega]
    have u1 : OeisA100434.d (2*k+4) = -6 * OeisA100434.d (2*k+2) - OeisA100434.d (2*k) := by rfl
    have u2 : OeisA100434.d (2*k+5) = -6 * OeisA100434.d (2*k+3) - OeisA100434.d (2*k+1) := by rfl
    have u3 : OeisA100434.c (2*k+4) = -6 * OeisA100434.c (2*k+2) - OeisA100434.c (2*k) := by rfl
    rw [u1, u2, u3]
    linarith

theorem swarm_proof : ∀ (n : ℕ), OeisA100434.g n + OeisA100434.a n = OeisA100434.b n := by
  intro n
  by_cases h : n % 2 = 0
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have hg : OeisA100434.g n = 0 := by
      rw [OeisA100434.g, if_pos h]
    have hb : OeisA100434.b n = -OeisA100434.c (2 * k + 1) := by
      rw [OeisA100434.b, if_pos h]
      rw [show n + 1 = 2 * k + 1 by omega]
    rw [hg, hb, hk, OeisA100434.a_even k]
    ring
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have hg : OeisA100434.g n = OeisA100434.c n := by
      rw [OeisA100434.g, if_neg h]
    have hb : OeisA100434.b n = OeisA100434.c (2 * k) := by
      rw [OeisA100434.b, if_neg h]
      rw [show n - 1 = 2 * k by omega]
    rw [hg, hb, hk, OeisA100434.a_odd k]
    exact Bl k
