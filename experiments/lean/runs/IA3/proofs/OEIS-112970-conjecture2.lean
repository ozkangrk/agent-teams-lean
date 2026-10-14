import FormalConjectures.OEIS.«112970»

/-! Swarm proof for OEIS A112970 conjecture2: a (2^n - 1) = a (3 * 2^n - 1).
Both sides equal 1: odd unfold chains down to a 0 resp. a 2. -/

theorem swarm_proof : ∀ (n : ℕ), OeisA112970.a (2 ^ n - 1) = OeisA112970.a (3 * 2 ^ n - 1) := by
  intro n
  have keyodd : ∀ m : ℕ, 3 ≤ m → m % 2 = 1 → OeisA112970.a m = OeisA112970.a (m / 2) := by
    intro m hm hmod
    rw [OeisA112970.a, if_neg (show m ≠ 0 by omega), if_neg (show m ≠ 1 by omega), if_pos hmod]
  have a_m1 : ∀ n : ℕ, OeisA112970.a (2 ^ n - 1) = 1 := by
    intro n
    induction n with
    | zero => rw [OeisA112970.a, if_pos (by decide)]
    | succ n ih =>
      by_cases hn : n = 0
      · subst hn; rw [OeisA112970.a, if_neg (by decide), if_pos (by decide)]
      · have hA : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
        have hge : 4 ≤ 2 * 2 ^ n := by
          have h2n2 : 2 ≤ 2 ^ n :=
            Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 1 ≤ n by omega)
          omega
        have hmod : (2 ^ (n + 1) - 1) % 2 = 1 := by omega
        have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by omega
        have hge3 : 3 ≤ 2 ^ (n + 1) - 1 := by omega
        rw [keyodd (2 ^ (n + 1) - 1) hge3 hmod, hdiv]
        exact ih
  have a_3m1 : ∀ n : ℕ, OeisA112970.a (3 * 2 ^ n - 1) = 1 := by
    intro n
    induction n with
    | zero =>
      have a1v : OeisA112970.a 1 = 1 := by
        rw [OeisA112970.a, if_neg (by decide), if_pos (by decide)]
      have h2 : OeisA112970.a 2 = OeisA112970.a 1 := by
        rw [OeisA112970.a, if_neg (by decide), if_neg (by decide),
          if_neg (show (2 : ℕ) % 2 ≠ 1 by decide)]
        rfl
      rw [show 3 * 2 ^ 0 - 1 = 2 from by norm_num, h2, a1v]
    | succ n ih =>
      have hA : 3 * 2 ^ (n + 1) = 2 * (3 * 2 ^ n) := by rw [Nat.pow_succ]; ring
      have h3 : 3 ≤ 3 * 2 ^ n := Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow (n := n))
      have hge : 4 ≤ 3 * 2 ^ (n + 1) - 1 := by omega
      have hmod : (3 * 2 ^ (n + 1) - 1) % 2 = 1 := by omega
      have hdiv : (3 * 2 ^ (n + 1) - 1) / 2 = 3 * 2 ^ n - 1 := by omega
      have hge3 : 3 ≤ 3 * 2 ^ (n + 1) - 1 := by omega
      rw [keyodd (3 * 2 ^ (n + 1) - 1) hge3 hmod, hdiv]
      exact ih
  rw [a_m1 n, a_3m1 n]
