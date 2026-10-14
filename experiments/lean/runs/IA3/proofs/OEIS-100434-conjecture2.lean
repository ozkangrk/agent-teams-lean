import FormalConjectures.OEIS.«100434»

/-! Swarm proof for OEIS A100434 conjecture2. -/

namespace S100434C2

open OeisA100434

theorem d_rec (n : ℕ) : d (n + 4) = -6 * d (n + 2) - d n := rfl

theorem d_even : ∀ n : ℕ, ∃ t : ℤ, d n = 2 * t := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨-5, rfl⟩
      · exact ⟨-12, rfl⟩
    · have hr : d n = -6 * d (n - 2) - d (n - 4) := by
        have h := d_rec (n - 4)
        rwa [show (n - 4) + 4 = n from by omega, show (n - 4) + 2 = n - 2 from by omega] at h
      obtain ⟨a, ha⟩ := ih (n - 2) (by omega)
      obtain ⟨b, hb⟩ := ih (n - 4) (by omega)
      rw [hr, ha, hb]
      exact ⟨-6 * a - b, by ring⟩

theorem key_even : ∀ k : ℕ, d (2 * k) + d (2 * k + 1) = -2 * c (2 * k + 1) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h_eq2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have h_eq : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [h_eq2, h_eq]
    have hd1 : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := rfl
    have hd2 : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := rfl
    have hc2 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := rfl
    rw [hd1, hd2, hc2]
    have ih2' : d (2 * k + 2) + d (2 * k + 3) = -2 * c (2 * k + 3) := by
      have h_eq_ih : 2 * (k + 1) = 2 * k + 2 := by omega
      have h_eq2_ih : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [← h_eq2_ih, ← h_eq_ih]
      exact ih2
    linarith [ih1, ih2']

theorem key_odd : ∀ k : ℕ, d (2 * k + 1) - d (2 * k) = 2 * c (2 * k) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have h_eq2 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have h_eq : 2 * (k + 2) = 2 * k + 4 := by omega
    rw [h_eq2, h_eq]
    have hd1 : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := rfl
    have hd2 : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := rfl
    have hc2 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := rfl
    rw [hd1, hd2, hc2]
    have ih2' : d (2 * k + 3) - d (2 * k + 2) = 2 * c (2 * k + 2) := by
      have h_eq_ih : 2 * (k + 1) = 2 * k + 2 := by omega
      have h_eq2_ih : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [← h_eq2_ih, ← h_eq_ih]
      exact ih2
    linarith [ih1, ih2']

theorem main : ∀ (n : ℕ), e n + f n = b n := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    rw [show k + k = 2 * k from by omega]
    have hmod : (2 * k) % 2 = 0 := by omega
    have hdiv : (2 * k) / 2 = k := by omega
    rw [f, hdiv, e, if_pos hmod, b, if_pos hmod]
    obtain ⟨u, hu⟩ := d_even (2 * k)
    obtain ⟨v, hv⟩ := d_even (2 * k + 1)
    have hkey := key_even k
    rw [hu, hv] at hkey
    rw [hu, hv]
    omega
  · subst hk
    have hne : (2 * k + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * k + 1) / 2 = k := by omega
    have hsub : 2 * k + 1 - 1 = 2 * k := by omega
    rw [f, hdiv, e, if_neg hne, b, if_neg hne, hsub]
    obtain ⟨u, hu⟩ := d_even (2 * k)
    obtain ⟨v, hv⟩ := d_even (2 * k + 1)
    have hkey := key_odd k
    rw [hu, hv] at hkey
    rw [hu, hv]
    omega

end S100434C2

theorem swarm_proof : ∀ (n : ℕ), OeisA100434.e n + OeisA100434.f n = OeisA100434.b n :=
  S100434C2.main
