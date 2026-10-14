import FormalConjectures.OEIS.«100434»

open OeisA100434

theorem K : ∀ k : ℕ, d (2 * k + 1) - d (2 * k) = 2 * c (2 * k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have hA : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have hB : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [hA, hB]
    have hd4 : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := by rfl
    have hd5 : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := by rfl
    have hc4 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := by rfl
    rw [hd5, hd4, hc4]
    have h2a : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have h2b : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2a, h2b] at ih2
    linarith

theorem M : ∀ k : ℕ, c (2 * k + 1) + c (2 * k) = -d (2 * k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have hA : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have hB : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [hA, hB]
    have hc4 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := by rfl
    have hc5 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by rfl
    have hd4 : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := by rfl
    rw [hc5, hc4, hd4]
    have h2a : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have h2b : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2a, h2b] at ih2
    linarith

theorem Par : ∀ k : ℕ, (2 : ℤ) ∣ d (2 * k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨1, rfl⟩
  | one => exact ⟨-5, rfl⟩
  | more k ih1 ih2 =>
    have hB : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [hB]
    have hd4 : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := by rfl
    rw [hd4]
    obtain ⟨t1, h1⟩ := ih1
    obtain ⟨t2, h2⟩ := ih2
    have h2b : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2b] at h2
    rw [h1, h2]
    exact ⟨-6 * t2 - t1, by ring⟩
theorem N : ∀ k : ℕ, c (2 * k + 1) + d (2 * k + 1) = c (2 * k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have hA : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have hB : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [hA, hB]
    have hc5 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by rfl
    have hd5 : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := by rfl
    have hc4 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := by rfl
    rw [hc5, hd5, hc4]
    have h2a : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have h2b : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h2a, h2b] at ih2
    linarith

theorem swarm_proof : ∀ (n : ℕ), g n + a n = b n := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hn : n = 2 * k := by omega
    subst hn
    have hmod : (2 * k) % 2 = 0 := by omega
    rw [g, if_pos hmod, b, if_pos hmod, zero_add, a_even]
  · have hn : n = 2 * k + 1 := by omega
    subst hn
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    have hmodne : (2 * k + 1) % 2 ≠ 0 := by omega
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [g, if_neg hmodne, b, hmod, if_neg (by decide), hsub, a_odd, N]
