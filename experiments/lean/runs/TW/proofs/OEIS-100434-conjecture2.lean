import FormalConjectures.OEIS.«100434»

open OeisA100434

private lemma d_ee (k : ℕ) : d (2*k) = 2 * (d (2*k) / 2) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have e0 : 2*(k+2) = 2*k+4 := by omega
    rw [e0]
    have f0 : 2*(k+1) = 2*k+2 := by omega
    rw [f0] at ih2
    have hr : d (2*k+4) = -6 * d (2*k+2) - d (2*k) := by rfl
    rw [hr, ih2, ih1]
    omega

private lemma d_eo (k : ℕ) : d (2*k+1) = 2 * (d (2*k+1) / 2) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have e1 : 2*(k+2)+1 = 2*k+5 := by omega
    rw [e1]
    have f1 : 2*(k+1)+1 = 2*k+3 := by omega
    rw [f1] at ih2
    have hr : d (2*k+5) = -6 * d (2*k+3) - d (2*k+1) := by rfl
    rw [hr, ih2, ih1]
    omega

private lemma d_even (n : ℕ) : d n = 2 * (d n / 2) := by
  cases Nat.mod_two_eq_zero_or_one n with
  | inl h => obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
             subst hk; exact d_ee k
  | inr h => obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
             subst hk; exact d_eo k

private lemma E2 (k : ℕ) : d (2*k) / 2 + d (2*k+1) / 2 = - c (2*k+1) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have e1 : 2*(k+2)+1 = 2*k+5 := by omega
    have e0 : 2*(k+2) = 2*k+4 := by omega
    rw [e1, e0]
    have f1 : 2*(k+1)+1 = 2*k+3 := by omega
    have f0 : 2*(k+1) = 2*k+2 := by omega
    rw [f1, f0] at ih2
    have hrd4 : d (2*k+4) = -6 * d (2*k+2) - d (2*k) := by rfl
    have hrd5 : d (2*k+5) = -6 * d (2*k+3) - d (2*k+1) := by rfl
    have hrc5 : c (2*k+5) = -6 * c (2*k+3) - c (2*k+1) := by rfl
    rw [hrd4, hrd5, hrc5]
    rw [d_even (2*k+2), d_even (2*k), d_even (2*k+3), d_even (2*k+1)]
    omega

private lemma O2 (k : ℕ) : -(d (2*k) / 2) + d (2*k+1) / 2 = c (2*k) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have e1 : 2*(k+2)+1 = 2*k+5 := by omega
    have e0 : 2*(k+2) = 2*k+4 := by omega
    rw [e1, e0]
    have f1 : 2*(k+1)+1 = 2*k+3 := by omega
    have f0 : 2*(k+1) = 2*k+2 := by omega
    rw [f1, f0] at ih2
    have hrd4 : d (2*k+4) = -6 * d (2*k+2) - d (2*k) := by rfl
    have hrd5 : d (2*k+5) = -6 * d (2*k+3) - d (2*k+1) := by rfl
    have hrc4 : c (2*k+4) = -6 * c (2*k+2) - c (2*k) := by rfl
    rw [hrd4, hrd5, hrc4]
    rw [d_even (2*k+2), d_even (2*k), d_even (2*k+3), d_even (2*k+1)]
    omega

theorem swarm_proof : ∀ (n : ℕ), e n + f n = b n := by
  intro n
  cases Nat.mod_two_eq_zero_or_one n with
  | inl h =>
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    subst hk
    have hne0 : (2*k) % 2 = 0 := by omega
    have he : e (2*k) = d (2*k) / 2 := by unfold e; rw [if_pos hne0]
    have hf : f (2*k) = d (2*k+1) / 2 := by
      show d (2 * ((2*k)/2) + 1) / 2 = d (2*k+1) / 2
      have hd : (2*k)/2 = k := by omega
      rw [hd]
    have hb : b (2*k) = - c (2*k+1) := by unfold b; rw [if_pos hne0]
    rw [he, hf, hb]
    exact E2 k
  | inr h =>
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    subst hk
    have hne : ¬ ((2*k+1) % 2 = 0) := by omega
    have hd1 : 2*k+1-1 = 2*k := by omega
    have hd2 : (2*k+1)/2 = k := by omega
    have he : e (2*k+1) = -(d (2*k+1-1) / 2) := by unfold e; rw [if_neg hne]
    have hf : f (2*k+1) = d (2*k+1) / 2 := by
      show d (2 * ((2*k+1)/2) + 1) / 2 = d (2*k+1) / 2
      rw [hd2]
    have hb : b (2*k+1) = c (2*k) := by
      unfold b
      rw [if_neg hne, hd1]
    rw [he, hf, hb]
    exact O2 k
