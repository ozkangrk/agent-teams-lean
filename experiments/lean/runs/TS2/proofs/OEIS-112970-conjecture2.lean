import FormalConjectures.OEIS.«112970»

open OeisA112970

theorem a_odd_step (m : ℕ) (h1 : 1 < m) (hodd : m % 2 = 1) : a m = a (m / 2) := by
  conv_lhs => unfold a
  rw [if_neg (by omega), if_neg (by omega), if_pos hodd]

theorem a_two_pow_sub_one (k : ℕ) : a (2^k - 1) = 1 := by
  induction k with
  | zero => unfold a; rfl
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · unfold a; rfl
    · have h2 : (2:ℕ) ≤ 2^k := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ k by omega)
      have hp : (2:ℕ)^(k+1) = 2 * (2:ℕ)^k := by rw [Nat.pow_succ]; ring
      rw [show (2:ℕ)^(k+1) - 1 = 2 * ((2:ℕ)^k - 1) + 1 from by omega]
      rw [a_odd_step _ (by omega) (by omega)]
      rw [show (2 * ((2:ℕ)^k - 1) + 1) / 2 = (2:ℕ)^k - 1 from by omega]
      exact ih

theorem swarm_proof (n : ℕ) : a (2^n - 1) = a (3 * 2^n - 1) := by
  have key : ∀ m : ℕ, a (3 * 2^m - 1) = 1 := by
    intro m
    induction m with
    | zero => unfold a; unfold a; rfl
    | succ m ih =>
      have h2 : (1:ℕ) ≤ 2^m := Nat.one_le_two_pow
      have hp : (2:ℕ)^(m+1) = 2 * (2:ℕ)^m := by rw [Nat.pow_succ]; ring
      rw [show (3:ℕ) * 2^(m+1) - 1 = 2 * (3 * (2:ℕ)^m - 1) + 1 from by omega]
      rw [a_odd_step _ (by omega) (by omega)]
      rw [show (2 * (3 * (2:ℕ)^m - 1) + 1) / 2 = 3 * (2:ℕ)^m - 1 from by omega]
      exact ih
  rw [a_two_pow_sub_one, key]
