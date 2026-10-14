import FormalConjectures.OEIS.«70823»

open OeisA70823

set_option maxRecDepth 100000 in
theorem swarm_proof :
    answer(False) ↔ ∀ n : ℕ, 2 < n →
      a n ≡ 0 [MOD 3] ∧
        ∃ j k s : ℕ, a n = 2 ^ j * 3 ^ k * s ∧ Squarefree s := by
  constructor
  · intro h
    exact False.elim h
  · intro hall
    obtain ⟨-, j1, k1, s1, hEq, hsq⟩ := hall 20 (by norm_num)
    have hd : (169:ℕ) ∣ a 20 := by
      rw [Nat.dvd_iff_mod_eq_zero]
      decide
    rw [hEq] at hd
    have hc13 : (13:ℕ).Prime := by norm_num
    have hc : Nat.Coprime (13:ℕ) (2 ^ j1 * 3 ^ k1) := by
      rw [Nat.Prime.coprime_iff_not_dvd hc13]
      intro h
      rcases (Nat.Prime.dvd_mul hc13).mp h with h' | h'
      · exact absurd (Nat.Prime.dvd_of_dvd_pow hc13 h') (by norm_num)
      · exact absurd (Nat.Prime.dvd_of_dvd_pow hc13 h') (by norm_num)
    have hc169 : Nat.Coprime (169:ℕ) (2 ^ j1 * 3 ^ k1) := by
      have := Nat.Coprime.pow_left 2 hc
      simpa using this
    have hd2 : (13:ℕ) * 13 ∣ s1 := by
      have := Nat.Coprime.dvd_of_dvd_mul_left hc169 hd
      simpa using this
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 13 hc13 hd2).elim
