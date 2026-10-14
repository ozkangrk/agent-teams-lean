
import FormalConjectures.OEIS.«113252»

open OeisA113252

def c : ℕ → ℤ
  | 0 => 2
  | 1 => 28
  | n + 2 => -4 * c (n + 1) - 36 * c n

theorem swarm_proof : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  have harec : ∀ k : ℕ, a (k + 4) = -4 * a (k + 3) + 144 * a (k + 1) + 1296 * a k := by
    intro k; simp only [a]
  have key : ∀ m : ℕ,
      a (2 * m + 1) = (c m) ^ 2 ∧
      (a (2 * m) : ℚ) = (17 / 576 : ℚ) * ((c m : ℚ)) ^ 2
        + (23 / 10368 : ℚ) * ((c (m + 1) : ℚ)) ^ 2
        + (-7 / 82944 : ℚ) * ((c (m + 2) : ℚ)) ^ 2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | n
      · constructor
        · rfl
        · norm_num [c, a]
      rcases n with _ | n
      · constructor
        · rfl
        · norm_num [c, a]
      -- here the goal is about n + 2, with n ≥ 1
      have h1 := ih (n + 1) (by omega)
      have h3 := ih n (by omega)
      have e2 : c (n + 2) = -4 * c (n + 1) - 36 * c n := by simp only [c]
      have e3 : c (n + 3) = -4 * c (n + 2) - 36 * c (n + 1) := by
        rw [show n + 3 = (n + 1) + 2 from by omega]; simp only [c]
      have e4 : c (n + 4) = -4 * c (n + 3) - 36 * c (n + 2) := by
        rw [show n + 4 = (n + 2) + 2 from by omega]; simp only [c]
      -- even part
      have hE : ((a (2 * (n + 2)) : ℚ)) = (17 / 576 : ℚ) * ((c (n + 2) : ℚ)) ^ 2
        + (23 / 10368 : ℚ) * ((c (n + 3) : ℚ)) ^ 2
        + (-7 / 82944 : ℚ) * ((c (n + 4) : ℚ)) ^ 2 := by
        rw [show a (2 * (n + 2)) = -4 * a (2 * (n + 1) + 1) + 144 * a (2 * n + 1) + 1296 * a (2 * n) from by
              have h := harec (2 * n)
              rw [show 2 * (n + 2) = 2 * n + 4 from by omega] at *
              omega]
        rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by omega]
        have := h1.1
        rw [show 2 * (n + 1) + 1 = 2 * n + 3 from by omega] at this
        rw [this, h3.1]
        push_cast
        rw [h3.2, e4, e3, e2]
        push_cast
        ring
      -- odd part
      have hO : a (2 * (n + 2) + 1) = (c (n + 2)) ^ 2 := by
        have h' : a (2 * (n + 2) + 1) = -4 * a (2 * (n + 2)) + 144 * a (2 * (n + 1))
            + 1296 * a (2 * n + 1) := by
          conv_lhs => rw [show 2 * (n + 2) + 1 = (2 * n + 1) + 4 from by omega]
          rw [harec (2 * n + 1)]
          rw [show 2 * n + 1 + 3 = 2 * (n + 2) from by omega,
              show 2 * n + 1 + 1 = 2 * (n + 1) from by omega]
        rw [h', h3.1]
        suffices hQ : (((-4 * a (2 * (n + 2)) + 144 * a (2 * (n + 1)) + 1296 * (c n) ^ 2 : ℤ) : ℚ)
            = ((c (n + 2) : ℚ)) ^ 2) by exact_mod_cast hQ
        push_cast
        rw [hE, h1.2, e4, e3, e2]
        push_cast
        ring
      exact ⟨hO, hE⟩
  intro n
  exact ⟨c n, by rw [(key n).1, pow_two]⟩
