import FormalConjectures.OEIS.«100434»

open OeisA100434

theorem key2 : ∀ m : ℕ, ∃ u v : ℤ, d (2 * m) = 2 * u ∧ d (2 * m + 1) = 2 * v ∧
    u + v = -c (2 * m + 1) ∧ v - u = c (2 * m) := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero =>
    refine ⟨1, 2, by rfl, by rfl, by rfl, by rfl⟩
  | one =>
    refine ⟨-5, -12, by rfl, by rfl, by rfl, by rfl⟩
  | more k ih1 ih2 =>
    obtain ⟨u, v, hd0, hd1, hsum, hdiff⟩ := ih1
    obtain ⟨u', v', hd0', hd1', hsum', hdiff'⟩ := ih2
    have h0' : d (2 * k + 2) = 2 * u' := by
      rw [show 2 * k + 2 = 2 * (k + 1) from by omega]; exact hd0'
    have h1' : d (2 * k + 3) = 2 * v' := by
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by omega]; exact hd1'
    have hsum2 : u' + v' = -c (2 * k + 3) := by
      rw [show 2 * k + 3 = 2 * (k + 1) + 1 from by omega]; exact hsum'
    have hdiff2 : v' - u' = c (2 * k + 2) := by
      rw [show 2 * k + 2 = 2 * (k + 1) from by omega]; exact hdiff'
    refine ⟨-6 * u' - u, -6 * v' - v, ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (k + 2) = 2 * k + 4 from by omega]
      have hd : d (2 * k + 4) = -6 * d (2 * k + 2) - d (2 * k) := by rfl
      rw [hd, h0', hd0]; ring
    · rw [show 2 * (k + 2) + 1 = 2 * k + 5 from by omega]
      have hd : d (2 * k + 5) = -6 * d (2 * k + 3) - d (2 * k + 1) := by rfl
      rw [hd, h1', hd1]; ring
    · rw [show 2 * (k + 2) + 1 = 2 * k + 5 from by omega]
      have hc : c (2 * k + 5) = -6 * c (2 * k + 3) - c (2 * k + 1) := by rfl
      linarith [hc, hsum2, hsum]
    · rw [show 2 * (k + 2) = 2 * k + 4 from by omega]
      have hc : c (2 * k + 4) = -6 * c (2 * k + 2) - c (2 * k) := by rfl
      linarith [hc, hdiff2, hdiff]

theorem swarm_proof (n : ℕ) : e n + f n = b n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · obtain ⟨u, v, hd0, hd1, hsum, hdiff⟩ := key2 m
    rw [show m + m = 2 * m from by omega]
    have he : e (2 * m) = u := by
      rw [e]
      rw [if_pos (by omega : (2 * m) % 2 = 0)]
      rw [hd0]; omega
    have hf : f (2 * m) = v := by
      rw [f]
      rw [show (2 * m) / 2 = m from by omega]
      rw [hd1]; omega
    have hb : b (2 * m) = -c (2 * m + 1) := by
      rw [b, if_pos (by omega : (2 * m) % 2 = 0)]
    rw [he, hf, hb]; exact hsum
  · obtain ⟨u, v, hd0, hd1, hsum, hdiff⟩ := key2 m
    have he : e (2 * m + 1) = -u := by
      rw [e]
      rw [if_neg (by omega : ¬ ((2 * m + 1) % 2 = 0))]
      rw [show (2 * m + 1) - 1 = 2 * m from by omega]
      rw [hd0]; omega
    have hf : f (2 * m + 1) = v := by
      rw [f]
      rw [show (2 * m + 1) / 2 = m from by omega]
      rw [hd1]; omega
    have hb : b (2 * m + 1) = c (2 * m) := by
      rw [b, if_neg (by omega : ¬ ((2 * m + 1) % 2 = 0))]
      rw [show (2 * m + 1) - 1 = 2 * m from by omega]
    rw [he, hf, hb]; linarith
