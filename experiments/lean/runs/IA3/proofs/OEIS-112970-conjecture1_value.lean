import FormalConjectures.OEIS.«112970»

/-! Swarm proof for OEIS A112970 conjecture1_value: a (2^n) = n^2 / 4 + 1.
Main recurrence a(2^(n+1)) = a(2^n) + a(2^n - 2) (n >= 1); helper
a(2^(m+1) - 2) = m/2 + 1 by two-step induction. -/

theorem swarm_proof : ∀ n : ℕ, OeisA112970.a (2 ^ n) = n ^ 2 / 4 + 1 := by
  intro n
  have keyodd : ∀ m : ℕ, 3 ≤ m → m % 2 = 1 → OeisA112970.a m = OeisA112970.a (m / 2) := by
    intro m hm hmod
    rw [OeisA112970.a, if_neg (show m ≠ 0 by omega), if_neg (show m ≠ 1 by omega), if_pos hmod]
  have keyodd' : ∀ m : ℕ, m % 2 = 1 → OeisA112970.a m = OeisA112970.a (m / 2) := by
    intro m hmod
    by_cases hm : m = 1
    · subst hm
      have a1 : OeisA112970.a 1 = 1 := by
        rw [OeisA112970.a, if_neg (by decide), if_pos (by decide)]
      have a0 : OeisA112970.a 0 = 1 := by
        rw [OeisA112970.a, if_pos (by decide)]
      show OeisA112970.a 1 = OeisA112970.a 0
      rw [a1, a0]
    · exact keyodd m (by omega) hmod
  have keyeven : ∀ m : ℕ, 4 ≤ m → m % 2 = 0 →
      OeisA112970.a m = OeisA112970.a (m / 2) + OeisA112970.a (m / 2 - 2) := by
    intro m hm hmod
    rw [OeisA112970.a, if_neg (show m ≠ 0 by omega), if_neg (show m ≠ 1 by omega),
      if_neg (show m % 2 ≠ 1 by omega)]
    have hk2 : ¬ (m / 2 < 2) := by omega
    rw [if_neg hk2]
  have a_m1 : ∀ n : ℕ, OeisA112970.a (2 ^ n - 1) = 1 := by
    intro n
    induction n with
    | zero => rw [OeisA112970.a, if_pos (by decide)]
    | succ n ih =>
      by_cases hn : n = 0
      · subst hn; rw [OeisA112970.a, if_neg (by decide), if_pos (by decide)]
      · have hA : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
        have hge : 4 ≤ 2 * 2 ^ n := by
          have h2n2 : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 1 ≤ n by omega)
          omega
        have hmod : (2 ^ (n + 1) - 1) % 2 = 1 := by omega
        have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by omega
        have hge3 : 3 ≤ 2 ^ (n + 1) - 1 := by omega
        rw [keyodd (2 ^ (n + 1) - 1) hge3 hmod, hdiv]
        exact ih
  have bseq : ∀ n : ℕ, OeisA112970.a (2 ^ (n + 1) - 2) = n / 2 + 1 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      have h0 : OeisA112970.a (2 ^ (0 + 1) - 2) = 1 := by
        rw [show 2 ^ (0 + 1) - 2 = 0 from by norm_num]
        rw [OeisA112970.a, if_pos (by decide)]
      rw [h0]
    | one =>
      have a1v : OeisA112970.a 1 = 1 := by
        rw [OeisA112970.a, if_neg (by decide), if_pos (by decide)]
      have h2 : OeisA112970.a 2 = OeisA112970.a 1 := by
        rw [OeisA112970.a, if_neg (by decide), if_neg (by decide),
          if_neg (show (2 : ℕ) % 2 ≠ 1 by decide)]
        rfl
      rw [show 2 ^ (1 + 1) - 2 = 2 from by norm_num, h2, a1v]
    | more k ih1 ih2 =>
      have hA : 2 ^ (k + 3) = 2 * 2 ^ (k + 2) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hA2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hge : 6 ≤ 2 ^ (k + 3) - 2 := by
        have h1 : 2 ≤ 2 ^ (k + 1) :=
          Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 1 ≤ k + 1 by omega)
        omega
      have hmod : (2 ^ (k + 3) - 2) % 2 = 0 := by omega
      have hd1 : (2 ^ (k + 3) - 2) / 2 = 2 ^ (k + 2) - 1 := by omega
      have hval1 : OeisA112970.a (2 ^ (k + 2) - 1) = 1 := a_m1 (k + 2)
      have hodd : (2 ^ (k + 2) - 3) % 2 = 1 := by omega
      have hd2 : (2 ^ (k + 2) - 3) / 2 = 2 ^ (k + 1) - 2 := by omega
      have hd3 : 2 ^ (k + 2) - 1 - 2 = 2 ^ (k + 2) - 3 := by omega
      rw [keyeven (2 ^ (k + 3) - 2) (by omega) hmod, hd1, hval1, hd3, keyodd' _ hodd, hd2, ih1]
      omega
  -- main induction
  induction n with
  | zero =>
    have h1 : OeisA112970.a (2 ^ 0) = 1 := by
      rw [show 2 ^ 0 = 1 from by norm_num]
      rw [OeisA112970.a, if_neg (by decide), if_pos (by decide)]
    rw [h1]
    norm_num
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      have a1v : OeisA112970.a 1 = 1 := by
        rw [OeisA112970.a, if_neg (by decide), if_pos (by decide)]
      have h2 : OeisA112970.a 2 = OeisA112970.a 1 := by
        rw [OeisA112970.a, if_neg (by decide), if_neg (by decide),
          if_neg (show (2 : ℕ) % 2 ≠ 1 by decide)]
        rfl
      rw [show 2 ^ (0 + 1) = 2 from by norm_num, h2, a1v]
      norm_num
    · have hA : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
      have hge : 4 ≤ 2 ^ (n + 1) := by
        have h2n2 : 2 ≤ 2 ^ n := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 1 ≤ n by omega)
        omega
      have hmod : (2 ^ (n + 1)) % 2 = 0 := by omega
      have hd1 : 2 ^ (n + 1) / 2 = 2 ^ n := by omega
      have hb := bseq (n - 1)
      have hb' : OeisA112970.a (2 ^ n - 2) = (n - 1) / 2 + 1 := by
        have he : 2 ^ (n - 1 + 1) - 2 = 2 ^ n - 2 := by rw [show n - 1 + 1 = n from by omega]
        rw [he] at hb
        exact hb
      rw [keyeven (2 ^ (n + 1)) hge hmod, hd1, ih, hb']
      rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · have hs1 : (t + t) ^ 2 = 4 * (t * t) := by ring
        have hs2 : (t + t + 1) ^ 2 = 4 * (t * t) + 4 * t + 1 := by ring
        omega
      · have hs1 : (2 * t + 1) ^ 2 = 4 * (t * t) + 4 * t + 1 := by ring
        have hs2 : (2 * t + 1 + 1) ^ 2 = 4 * (t * t) + 8 * t + 4 := by ring
        omega
