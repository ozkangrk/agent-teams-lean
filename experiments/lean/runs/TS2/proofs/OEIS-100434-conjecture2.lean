import FormalConjectures.OEIS.«100434»

namespace OeisA100434

theorem drel (k : ℕ) :
    d (2 * k) = -(c (2 * k + 1)) - c (2 * k) ∧
    d (2 * k + 1) = c (2 * k) - c (2 * k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => constructor <;> decide
  | one => constructor <;> decide
  | more k ih1 ih2 =>
    have hde : d (2 * (k + 2)) = -6 * d (2 * k + 2) - d (2 * k) := by
      have hA : 2 * (k + 2) = 2 * k + 4 := by omega
      rw [hA]
      rfl
    have hdo : d (2 * (k + 2) + 1) = -6 * d (2 * k + 3) - d (2 * k + 1) := by
      have hA : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
      have hB : 2 * k + 5 = 2 * k + 1 + 4 := by omega
      rw [hA, hB]
      rfl
    have hce : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := rfl
    have hce2 : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by
      have hA : 2 * k + 5 = 2 * k + 1 + 4 := by omega
      rw [hA]
      rfl
    obtain ⟨ih1e, ih1o⟩ := ih1
    obtain ⟨ih2e, ih2o⟩ := ih2
    have e1 : d (2 * k + 2) = -(c (2 * k + 3)) - c (2 * k + 2) := by
      have hA : 2 * (k + 1) = 2 * k + 2 := by omega
      have hB : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [← hB, ← hA]
      exact ih2e
    have o1 : d (2 * k + 3) = c (2 * k + 2) - c (2 * k + 3) := by
      have hA : 2 * (k + 1) = 2 * k + 2 := by omega
      have hB : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      rw [← hB, ← hA]
      exact ih2o
    have hX : c (2 * (k + 2) + 1) = -6 * c (2 * k + 3) - c (2 * k + 1) := by
      rw [show 2 * (k + 2) + 1 = 2 * k + 5 from by omega]
      exact hce2
    have hY : c (2 * (k + 2)) = -6 * c (2 * k + 2) - c (2 * k) := by
      rw [show 2 * (k + 2) = 2 * k + 4 from by omega]
      exact hce
    constructor
    · rw [hde, e1, ih1e, hX, hY]
      ring
    · rw [hdo, o1, ih1o, hX, hY]
      ring

theorem dpar (k : ℕ) : d (2 * k) % 2 = 0 ∧ d (2 * k + 1) % 2 = 0 := by
  induction k using Nat.twoStepInduction with
  | zero => constructor <;> rfl
  | one => constructor <;> rfl
  | more k ih1 ih2 =>
    obtain ⟨i1e, i1o⟩ := ih1
    obtain ⟨i2e, i2o⟩ := ih2
    have h1 : d (2 * k + 2) % 2 = 0 := by
      rw [show 2 * k + 2 = 2 * (k + 1) from by omega]
      exact i2e
    have h2 : d (2 * k + 3) % 2 = 0 := by
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by omega]
      exact i2o
    have h3 : d (2 * k) % 2 = 0 := i1e
    have h4 : d (2 * k + 1) % 2 = 0 := i1o
    have hE : d (2 * (k + 2)) = -6 * d (2 * k + 2) - d (2 * k) := by
      have hA : 2 * (k + 2) = 2 * k + 4 := by omega
      rw [hA]
      rfl
    have hO : d (2 * (k + 2) + 1) = -6 * d (2 * k + 3) - d (2 * k + 1) := by
      have hA : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
      have hB : 2 * k + 5 = 2 * k + 1 + 4 := by omega
      rw [hA, hB]
      rfl
    constructor
    · rw [hE]
      omega
    · rw [hO]
      omega


theorem deven (n : ℕ) : d n % 2 = 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hq : n = 2 * k := by omega
    rw [hq]
    exact (dpar k).1
  · have hq : n = 2 * k + 1 := by omega
    rw [hq]
    exact (dpar k).2

theorem eeq (n : ℕ) :
    e n = if n % 2 = 0 then d n / 2 else -(d (n - 1) / 2) := rfl

theorem feq (n : ℕ) : f n = d (2 * (n / 2) + 1) / 2 := rfl

theorem beq (n : ℕ) :
    b n = if n % 2 = 0 then -(c (n + 1)) else c (n - 1) := rfl

theorem geq (n : ℕ) :
    g n = if n % 2 = 0 then 0 else c n := rfl

end OeisA100434

open OeisA100434

theorem swarm_proof : ∀ (n : ℕ), e n + f n = b n := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk' : n = 2 * k := by omega
    have hne : n % 2 = 0 := by omega
    have hbe : b n = -(c (n + 1)) := by rw [beq, if_pos hne]
    have h1 := (drel k).1
    rw [← hk'] at h1
    have h2 := (drel k).2
    rw [← hk'] at h2
    have hde : d n = -(c (n + 1)) - c n := h1
    have hdo : d (n + 1) = c n - c (n + 1) := h2
    have hdne : d n % 2 = 0 := deven n
    have hdno : d (n + 1) % 2 = 0 := deven (n + 1)
    have hE : e n = d n / 2 := by rw [eeq, if_pos hne]
    have hF : f n = d (n + 1) / 2 := by
      have hnm : n / 2 = k := by omega
      have hB : 2 * k + 1 = n + 1 := by omega
      rw [feq, hnm, hB]
    rw [hE, hF, hbe]
    omega
  · have hk' : n = 2 * k + 1 := by omega
    have hC : 2 * k = n - 1 := by omega
    have hno : n % 2 = 1 := by omega
    have hbe : b n = c (n - 1) := by rw [beq, if_neg (by omega : ¬ n % 2 = 0)]
    have h1 := (drel k).1
    rw [← hk'] at h1
    rw [hC] at h1
    have h2 := (drel k).2
    rw [← hk'] at h2
    rw [hC] at h2
    have hde : d (n - 1) = -(c n) - c (n - 1) := h1
    have hdo : d n = c (n - 1) - c n := h2
    have hdne : d (n - 1) % 2 = 0 := deven (n - 1)
    have hdno : d n % 2 = 0 := deven n
    have hE : e n = -(d (n - 1) / 2) := by rw [eeq, if_neg (by omega : ¬ n % 2 = 0)]
    have hF : f n = d n / 2 := by
      have hnm : n / 2 = k := by omega
      rw [feq, hnm, ← hk']
    rw [hE, hF, hbe]
    omega
