import FormalConjectures.OEIS.«100434»

open OeisA100434

private lemma cd (k : ℕ) : c (2*k+1) + d (2*k+1) = c (2*k) := by
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
    have hc : c (2*k+5) = -6 * c (2*k+3) - c (2*k+1) := by rfl
    have hd : d (2*k+5) = -6 * d (2*k+3) - d (2*k+1) := by rfl
    have hc4 : c (2*k+4) = -6 * c (2*k+2) - c (2*k) := by rfl
    rw [hc, hd, hc4]
    linarith [ih1, ih2]

theorem swarm_proof : ∀ (n : ℕ), g n + a n = b n := by
  intro n
  cases Nat.mod_two_eq_zero_or_one n with
  | inl h =>
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    subst hk
    have hne0 : (2*k) % 2 = 0 := by omega
    have hg : g (2*k) = 0 := by unfold g; rw [if_pos hne0]
    have hb : b (2*k) = - c (2*k+1) := by unfold b; rw [if_pos hne0]
    rw [hg, hb, a_even k]
    ring
  | inr h =>
    obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    subst hk
    have hne : ¬ ((2*k+1) % 2 = 0) := by omega
    have hg : g (2*k+1) = c (2*k+1) := by unfold g; rw [if_neg hne]
    have hb : b (2*k+1) = c (2*k+1-1) := by unfold b; rw [if_neg hne]
    have hsub : 2*k+1-1 = 2*k := by omega
    rw [hg, hb, hsub, a_odd k]
    exact cd k
