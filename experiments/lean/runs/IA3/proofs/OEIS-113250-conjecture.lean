import FormalConjectures.OEIS.«113250»

/-! Swarm proof for OEIS A113250. -/

namespace S113250

open OeisA113250

theorem a_rec (n : ℕ) : a (n + 4) = -4 * a (n + 3) + 64 * a (n + 1) + 256 * a n := rfl

theorem a6 : ∀ n : ℕ, a (n + 6) = 4096 * a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n <;> rfl
    · have e1 : a (n + 6) = -4 * a (n + 5) + 64 * a (n + 3) + 256 * a (n + 2) := a_rec (n + 2)
      have e2 : a (n + 5) = 4096 * a (n - 1) := by
        have h := ih (n - 1) (by omega)
        rwa [show (n - 1) + 6 = n + 5 from by omega] at h
      have e3 : a (n + 3) = 4096 * a (n - 3) := by
        have h := ih (n - 3) (by omega)
        rwa [show (n - 3) + 6 = n + 3 from by omega] at h
      have e4 : a (n + 2) = 4096 * a (n - 4) := by
        have h := ih (n - 4) (by omega)
        rwa [show (n - 4) + 6 = n + 2 from by omega] at h
      have e5 : a n = -4 * a (n - 1) + 64 * a (n - 3) + 256 * a (n - 4) := by
        have h := a_rec (n - 4)
        rwa [show (n - 4) + 4 = n from by omega, show (n - 4) + 3 = n - 1 from by omega,
          show (n - 4) + 1 = n - 3 from by omega] at h
      rw [e1, e2, e3, e4, e5]
      ring

theorem geom : ∀ q s : ℕ, a (2 * (3 * q + s) + 1) = 4096 ^ q * a (2 * s + 1) := by
  intro q s
  induction q with
  | zero => simp
  | succ k ih =>
    have e : 2 * (3 * (k + 1) + s) + 1 = (2 * (3 * k + s) + 1) + 6 := by ring
    rw [e, a6, ih, pow_succ]
    ring

theorem key : ∀ q e : ℕ, (4096 : ℤ) ^ q * ((2 : ℤ) ^ e * (2 : ℤ) ^ e)
    = ((2 : ℤ) ^ (6 * q + e)) * ((2 : ℤ) ^ (6 * q + e)) := by
  intro q e
  have h1 : (4096 : ℤ) ^ q = (2 : ℤ) ^ (12 * q) := by
    rw [show (4096 : ℤ) = (2 : ℤ) ^ (12 : ℕ) from rfl, ← pow_mul]
  rw [h1, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

theorem main : ∀ (n : ℕ), IsSquare (a (2 * n + 1)) := by
  intro n
  have hq : 3 * (n / 3) + n % 3 = n := Nat.div_add_mod n 3
  have hs3 : n % 3 < 3 := Nat.mod_lt n (y := 3) (by norm_num)
  have hval : a (2 * n + 1) = 4096 ^ (n / 3) * a (2 * (n % 3) + 1) := by
    have h := geom (n / 3) (n % 3)
    rwa [hq] at h
  interval_cases n % 3
  · refine ⟨(2 : ℕ) ^ (6 * (n / 3) + 1), ?_⟩
    rw [hval, show a (2 * 0 + 1) = (2 : ℕ) ^ (1 : ℕ) * (2 : ℕ) ^ (1 : ℕ) from rfl]
    exact key (n / 3) 1
  · refine ⟨(2 : ℕ) ^ (6 * (n / 3) + 3), ?_⟩
    rw [hval, show a (2 * 1 + 1) = (2 : ℕ) ^ (3 : ℕ) * (2 : ℕ) ^ (3 : ℕ) from rfl]
    exact key (n / 3) 3
  · refine ⟨(2 : ℕ) ^ (6 * (n / 3) + 6), ?_⟩
    rw [hval, show a (2 * 2 + 1) = (2 : ℕ) ^ (6 : ℕ) * (2 : ℕ) ^ (6 : ℕ) from rfl]
    exact key (n / 3) 6

end S113250

theorem swarm_proof : ∀ (n : ℕ), IsSquare (OeisA113250.a (2 * n + 1)) := S113250.main

