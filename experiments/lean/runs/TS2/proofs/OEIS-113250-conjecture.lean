import FormalConjectures.OEIS.«113250»

open OeisA113250

def f : ℕ → ℤ := fun n =>
  match n % 6 with
  | 0 => -1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => -1
  | _ => 4

theorem f_period (n : ℕ) : f (n + 6) = f n := by
  simp [f]

theorem f_rec (n : ℕ) : f (n + 4) = -f (n + 3) + f (n + 1) + f n := by
  have hb : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 6
  · have e4 : (n + 4) % 6 = 4 := by omega
    have e3 : (n + 3) % 6 = 3 := by omega
    have e1 : (n + 1) % 6 = 1 := by omega
    norm_num [f, h, e4, e3, e1]
  · have e4 : (n + 4) % 6 = 5 := by omega
    have e3 : (n + 3) % 6 = 4 := by omega
    have e1 : (n + 1) % 6 = 2 := by omega
    norm_num [f, h, e4, e3, e1]
  · have e4 : (n + 4) % 6 = 0 := by omega
    have e3 : (n + 3) % 6 = 5 := by omega
    have e1 : (n + 1) % 6 = 3 := by omega
    norm_num [f, h, e4, e3, e1]
  · have e4 : (n + 4) % 6 = 1 := by omega
    have e3 : (n + 3) % 6 = 0 := by omega
    have e1 : (n + 1) % 6 = 4 := by omega
    norm_num [f, h, e4, e3, e1]
  · have e4 : (n + 4) % 6 = 2 := by omega
    have e3 : (n + 3) % 6 = 1 := by omega
    have e1 : (n + 1) % 6 = 5 := by omega
    norm_num [f, h, e4, e3, e1]
  · have e4 : (n + 4) % 6 = 3 := by omega
    have e3 : (n + 3) % 6 = 2 := by omega
    have e1 : (n + 1) % 6 = 0 := by omega
    norm_num [f, h, e4, e3, e1]
theorem key : ∀ n : ℕ, a n = (4:ℤ)^n * f n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | (n+4) =>
      have h3 : a (n+4) = -4 * a (n+3) + 64 * a (n+1) + 256 * a n := by rfl
      have e1 : (4:ℤ)^(n+1) = (4:ℤ)^n * 4 := by rw [pow_succ]
      have e3 : (4:ℤ)^(n+3) = (4:ℤ)^n * 64 := by
        rw [show n+3 = n+1+2 from by omega, pow_add, e1]; ring
      have e4 : (4:ℤ)^(n+4) = (4:ℤ)^n * 256 := by
        rw [show n+4 = n+1+3 from by omega, pow_add, e1]; ring
      rw [h3, ih (n+3) (by omega), ih (n+1) (by omega), ih n (by omega), e4, e3, e1, f_rec]
      ring

theorem swarm_proof : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rw [key]
  have h4 : (4:ℤ)^(2*n+1) = ((2:ℤ)^(2*n+1)) * ((2:ℤ)^(2*n+1)) := by
    rw [show (4:ℤ) = (2:ℤ) * 2 from by norm_num, mul_pow]
  rw [h4]
  have hb : (2*n+1) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (2*n+1) % 6
  · omega
  · refine ⟨(2:ℤ)^(2*n+1), ?_⟩; simp only [f, h]; ring
  · omega
  · refine ⟨(2:ℤ)^(2*n+1), ?_⟩; simp only [f, h]; ring
  · omega
  · refine ⟨(2:ℤ)^(2*n+1) * 2, ?_⟩; simp only [f, h]; ring
