import FormalConjectures.OEIS.«113250»

open OeisA113250

def dc : ℕ → ℤ × ℤ
  | 0 => (2, 8)
  | j + 1 => (16 * (dc j).1 + 4 * (dc j).2, 0 * (dc j).2 - 64 * (dc j).1)

def dd (j : ℕ) : ℤ := (dc j).1
def cc (j : ℕ) : ℤ := (dc j).2

theorem dd_succ (j : ℕ) : dd (j + 1) = 16 * dd j + 4 * cc j := rfl
theorem cc_succ (j : ℕ) : cc (j + 1) = 0 * cc j - 64 * dd j := rfl

theorem a_rec (n : ℕ) : a (n + 4) = -4 * a (n + 3) + 64 * a (n + 1) + 256 * a n := rfl

theorem steppoly (D C U A1 A2 A3 A4 : ℚ) (h1 : A1 = D * D) (h2 : A2 = D * C + U) (h3 : A3 = C * C)
    (h4 : 12 * A4 = 256 * D * D - 128 * D * C - 32 * C * C)
    (h5 : 16 * D * D + 4 * D * C + C * C = 12 * U) :
    -4 * A4 + 64 * A2 + 256 * A1 = (16 * D + 4 * C) * (16 * D + 4 * C) ∧
    (-4 * (-4 * A4 + 64 * A2 + 256 * A1) + 64 * A3 + 256 * A2)
      = (16 * D + 4 * C) * (0 * C - 64 * D) + 256 * U ∧
    (-4 * (-4 * (-4 * A4 + 64 * A2 + 256 * A1) + 64 * A3 + 256 * A2) + 64 * A4 + 256 * A3)
      = (0 * C - 64 * D) * (0 * C - 64 * D) ∧
    12 * (-4 * (-4 * (-4 * (-4 * A4 + 64 * A2 + 256 * A1) + 64 * A3 + 256 * A2) + 64 * A4 + 256 * A3)
        + 64 * (-4 * A4 + 64 * A2 + 256 * A1) + 256 * A4)
      = 256 * (16 * D + 4 * C) * (16 * D + 4 * C) - 128 * (16 * D + 4 * C) * (0 * C - 64 * D)
        - 32 * (0 * C - 64 * D) * (0 * C - 64 * D) ∧
    16 * (16 * D + 4 * C) * (16 * D + 4 * C) + 4 * (16 * D + 4 * C) * (0 * C - 64 * D)
      + (0 * C - 64 * D) * (0 * C - 64 * D) = 12 * (256 * U) := by
  have A4v : A4 = (256 * D * D - 128 * D * C - 32 * C * C) / 12 := by linarith
  have Uv : U = (16 * D * D + 4 * D * C + C * C) / 12 := by linarith
  rw [h1, h2, h3, A4v, Uv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem key : ∀ j : ℕ,
    (a (4 * j + 1) : ℚ) = (dd j : ℚ) * (dd j : ℚ) ∧
    (a (4 * j + 2) : ℚ) = (dd j : ℚ) * (cc j : ℚ) + ((16 : ℚ) ^ (2 * j + 1) : ℚ) ∧
    (a (4 * j + 3) : ℚ) = (cc j : ℚ) * (cc j : ℚ) ∧
    12 * (a (4 * j + 4) : ℚ) = 256 * (dd j : ℚ) * (dd j : ℚ) - 128 * (dd j : ℚ) * (cc j : ℚ) - 32 * (cc j : ℚ) * (cc j : ℚ) ∧
    16 * (dd j : ℚ) * (dd j : ℚ) + 4 * (dd j : ℚ) * (cc j : ℚ) + (cc j : ℚ) * (cc j : ℚ) = 12 * ((16 : ℚ) ^ (2 * j + 1) : ℚ) := by
  intro j
  induction j with
  | zero => norm_num [dc, dd, cc, a]
  | succ j ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have hUp : (16 : ℚ) ^ (2 * (j + 1) + 1) = 256 * ((16 : ℚ) ^ (2 * j + 1) : ℚ) := by
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 from by omega, pow_add]
      ring
    have hdd : (dd (j + 1) : ℚ) = 16 * (dd j : ℚ) + 4 * (cc j : ℚ) := by
      rw [dd_succ]; push_cast; ring
    have hcc : (cc (j + 1) : ℚ) = 0 * (cc j : ℚ) - 64 * (dd j : ℚ) := by
      rw [cc_succ]; push_cast; ring
    have e5 : a (4 * j + 5) = -4 * a (4 * j + 4) + 64 * a (4 * j + 2) + 256 * a (4 * j + 1) := a_rec (4 * j + 1)
    have e6 : a (4 * j + 6) = -4 * a (4 * j + 5) + 64 * a (4 * j + 3) + 256 * a (4 * j + 2) := a_rec (4 * j + 2)
    have e7 : a (4 * j + 7) = -4 * a (4 * j + 6) + 64 * a (4 * j + 4) + 256 * a (4 * j + 3) := a_rec (4 * j + 3)
    have e8 : a (4 * j + 8) = -4 * a (4 * j + 7) + 64 * a (4 * j + 5) + 256 * a (4 * j + 4) := a_rec (4 * j + 4)
    have v5 : (a (4 * j + 5) : ℚ) = -4 * ((a (4 * j + 4) : ℚ)) + 64 * ((a (4 * j + 2) : ℚ)) + 256 * ((a (4 * j + 1) : ℚ)) := by
      rw [e5]; push_cast; try ring
    have v6 : (a (4 * j + 6) : ℚ) = -4 * (-4 * ((a (4 * j + 4) : ℚ)) + 64 * ((a (4 * j + 2) : ℚ)) + 256 * ((a (4 * j + 1) : ℚ))) + 64 * ((a (4 * j + 3) : ℚ)) + 256 * ((a (4 * j + 2) : ℚ)) := by
      rw [e6]; push_cast; rw [v5]; try ring
    have v7 : (a (4 * j + 7) : ℚ) = -4 * (-4 * (-4 * ((a (4 * j + 4) : ℚ)) + 64 * ((a (4 * j + 2) : ℚ)) + 256 * ((a (4 * j + 1) : ℚ))) + 64 * ((a (4 * j + 3) : ℚ)) + 256 * ((a (4 * j + 2) : ℚ))) + 64 * ((a (4 * j + 4) : ℚ)) + 256 * ((a (4 * j + 3) : ℚ)) := by
      rw [e7]; push_cast; rw [v6]; try ring
    have v8 : (a (4 * j + 8) : ℚ) = -4 * (-4 * (-4 * (-4 * ((a (4 * j + 4) : ℚ)) + 64 * ((a (4 * j + 2) : ℚ)) + 256 * ((a (4 * j + 1) : ℚ))) + 64 * ((a (4 * j + 3) : ℚ)) + 256 * ((a (4 * j + 2) : ℚ))) + 64 * ((a (4 * j + 4) : ℚ)) + 256 * ((a (4 * j + 3) : ℚ))) + 64 * (-4 * ((a (4 * j + 4) : ℚ)) + 64 * ((a (4 * j + 2) : ℚ)) + 256 * ((a (4 * j + 1) : ℚ))) + 256 * ((a (4 * j + 4) : ℚ)) := by
      rw [e8]; push_cast; rw [v7, v5]; try ring
    obtain ⟨s1, s2, s3, s4, s5⟩ := steppoly ((dd j : ℚ)) ((cc j : ℚ)) (((16 : ℚ) ^ (2 * j + 1) : ℚ))
      ((a (4 * j + 1) : ℚ)) ((a (4 * j + 2) : ℚ)) ((a (4 * j + 3) : ℚ)) ((a (4 * j + 4) : ℚ)) h1 h2 h3 h4 h5
    rw [show 4 * (j + 1) + 1 = 4 * j + 5 from by omega, show 4 * (j + 1) + 2 = 4 * j + 6 from by omega,
      show 4 * (j + 1) + 3 = 4 * j + 7 from by omega, show 4 * (j + 1) + 4 = 4 * j + 8 from by omega,
      hUp, hdd, hcc]
    exact ⟨by rw [v5]; exact s1, by rw [v6]; exact s2, by rw [v7]; exact s3, by rw [v8]; exact s4, s5⟩

theorem swarm_proof : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show 2 * (j + j) + 1 = 4 * j + 1 from by omega]
    have h := (key j).1
    exact ⟨dd j, Int.cast_injective (α := ℚ) (by rw [Int.cast_mul]; exact h)⟩
  · rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 from by omega]
    have h := (key j).2.2.1
    exact ⟨cc j, Int.cast_injective (α := ℚ) (by rw [Int.cast_mul]; exact h)⟩
