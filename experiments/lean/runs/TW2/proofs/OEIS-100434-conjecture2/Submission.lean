import FormalConjectures.OEIS.«100434»

open OeisA100434


theorem L2 (k : ℕ) : d (2 * k + 1) = c (2 * k) - c (2 * k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have ih2' : d (2 * k + 3) = c (2 * k + 2) - c (2 * k + 3) := by
      have e1 : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
      have e2 : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [e1, e2]; exact ih2
    show d (2 * k + 5) = c (2 * k + 4) - c (2 * k + 5)
    have hL : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := by rfl
    have hc5 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by rfl
    have hc4 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := by rfl
    linarith [hL, hc5, hc4, ih2', ih1]

theorem L1 (k : ℕ) : d (2 * k) = -(c (2 * k) + c (2 * k + 1)) := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k ih1 ih2 =>
    have ih2' : d (2 * k + 2) = -(c (2 * k + 2) + c (2 * k + 3)) := by
      have e1 : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
      have e2 : 2 * k + 2 = 2 * (k + 1) := by omega
      rw [e1, e2]; exact ih2
    show d (2 * k + 4) = -(c (2 * k + 4) + c (2 * k + 5))
    have hL : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := by rfl
    have hc5 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by rfl
    have hc4 : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := by rfl
    linarith [hL, hc5, hc4, ih2', ih1]

theorem coddQ : ∀ k, ((c k) % 2 = 1 ∧ (c (k + 2)) % 2 = 1) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨by rfl, by rfl⟩
  | one => exact ⟨by rfl, by rfl⟩
  | more k ih1 ih2 =>
    refine ⟨ih1.2, ?_⟩
    have h : c (k + 2 + 2) = -6 * c (k + 2) - c k := by rfl
    omega

theorem codd (n : ℕ) : (c n) % 2 = 1 := (coddQ n).1

theorem dodd (m : ℕ) : (d m) % 2 = 0 := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd m
  · rw [show m = 2 * k by omega]
    have h1 := codd (2 * k); have h2 := codd (2 * k + 1)
    rw [L1]; omega
  · rw [show m = 2 * k + 1 by omega]
    have h1 := codd (2 * k); have h2 := codd (2 * k + 1)
    rw [L2]; omega

theorem half (m : ℕ) (hm : (d m) % 2 = 0) : d m / 2 * 2 = d m := by
  have := EuclideanDomain.div_add_mod' (d m) 2
  omega

theorem swarm_proof (n : ℕ) : e n + f n = b n := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd n
  · rw [show n = 2 * k by omega]
    have hE : e (2 * k) = d (2 * k) / 2 := by
      simp only [e]
      split
      · next h => omega
      · next h => omega
    have hF : f (2 * k) = d (2 * k + 1) / 2 := by
      have hd : (2 * k) / 2 = k := by omega
      simp only [f]
      rw [hd]
    have hB : b (2 * k) = -c (2 * k + 1) := by
      simp only [b]
      split
      · rfl
      · next h => omega
    have hA2 := half (2 * k) (dodd (2 * k))
    have hB2 := half (2 * k + 1) (dodd (2 * k + 1))
    rw [hE, hF, hB]
    linarith [hA2, hB2, L1 k, L2 k]
  · rw [show n = 2 * k + 1 by omega]
    have hE : e (2 * k + 1) = -(d (2 * k) / 2) := by
      have e0 : 2 * k + 1 - 1 = 2 * k := by omega
      simp only [e]
      split
      · next h => omega
      · next h => first | rfl | (rw [e0]; rfl)
    have hF : f (2 * k + 1) = d (2 * k + 1) / 2 := by
      have hd : (2 * k + 1) / 2 = k := by omega
      simp only [f]
      rw [hd]
    have hB : b (2 * k + 1) = c (2 * k) := by
      simp only [b]
      split
      · next h => omega
      · next h => first | rfl | (congr 1; omega)
    have hA2 := half (2 * k) (dodd (2 * k))
    have hB2 := half (2 * k + 1) (dodd (2 * k + 1))
    rw [hB, hE, hF]
    linarith [hA2, hB2, L1 k, L2 k]

