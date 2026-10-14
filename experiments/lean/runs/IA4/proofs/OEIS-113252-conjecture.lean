import FormalConjectures.OEIS.«113252»

open OeisA113252

theorem scale6 : ∀ n : ℕ, a (n + 6) = 46656 * a n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases lt_or_ge n 6 with h6 | h6
    · interval_cases n <;> rfl
    · have e1 : a (n + 6) = -4 * a (n + 5) + 64 * a (n + 3) + 256 * a (n + 2) := by
        rw [show n + 6 = (n + 2) + 4 from by omega]; rfl
      have h5 : a (n + 5) = 46656 * a (n - 1) := by
        rw [show n + 5 = (n - 1) + 6 from by omega]; exact ih (n - 1) (by omega)
      have h3 : a (n + 3) = 46656 * a (n - 3) := by
        rw [show n + 3 = (n - 3) + 6 from by omega]; exact ih (n - 3) (by omega)
      have h2 : a (n + 2) = 46656 * a (n - 4) := by
        rw [show n + 2 = (n - 4) + 6 from by omega]; exact ih (n - 4) (by omega)
      have e2 : a n = -4 * a (n - 1) + 64 * a (n - 3) + 256 * a (n - 4) := by
        have hstep : a ((n - 4) + 4) = -4 * a ((n - 4) + 3) + 64 * a ((n - 4) + 1) + 256 * a (n - 4) := by rfl
        have ha1 : a ((n - 4) + 3) = a (n - 1) := by rw [show (n - 4) + 3 = n - 1 from by omega]
        have ha2 : a ((n - 4) + 1) = a (n - 3) := by rw [show (n - 4) + 1 = n - 3 from by omega]
        have ha0 : a ((n - 4) + 4) = a n := by rw [show (n - 4) + 4 = n from by omega]
        rw [ha0] at hstep
        rw [ha1] at hstep
        rw [ha2] at hstep
        exact hstep
      rw [e1, h5, h3, h2, e2]
      ring

theorem shift6 (r : ℕ) : ∀ m : ℕ, a (6 * m + r) = (46656 : ℤ) ^ m * a r := by
  intro m
  induction m with
  | zero => rw [show 6 * 0 + r = r from by omega, pow_zero, one_mul]
  | succ k ih =>
    rw [show 6 * (k + 1) + r = (6 * k + r) + 6 from by omega, scale6 (6 * k + r), ih,
      pow_succ]
    ring

theorem swarm_proof : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  have hdmd : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
  have hmod : n % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases h : n % 3
  · have hidx : 2 * n + 1 = 6 * (n / 3) + 1 := by omega
    rw [hidx, shift6 1]
    have ha1 : a 1 = 4 := rfl
    rw [ha1]
    refine ⟨2 * (216 : ℤ) ^ (n / 3), ?_⟩
    rw [show (46656 : ℤ) = 216 * 216 from by norm_num, mul_pow]
    ring
  · have hidx : 2 * n + 1 = 6 * (n / 3) + 3 := by omega
    rw [hidx, shift6 3]
    have ha3 : a 3 = 784 := rfl
    rw [ha3]
    refine ⟨28 * (216 : ℤ) ^ (n / 3), ?_⟩
    rw [show (46656 : ℤ) = 216 * 216 from by norm_num, mul_pow]
    ring
  · have hidx : 2 * n + 1 = 6 * (n / 3) + 5 := by omega
    rw [hidx, shift6 5]
    have ha5 : a 5 = 46656 := by rfl
    rw [ha5]
    refine ⟨184 * (216 : ℤ) ^ (n / 3), ?_⟩
    rw [show (46656 : ℤ) = 216 * 216 from by norm_num, mul_pow]
    ring
