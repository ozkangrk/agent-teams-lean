import FormalConjectures.OEIS.«70823»

set_option exponentiation.threshold 10000
set_option maxRecDepth 20000

theorem swarm_proof :
    answer(False) ↔ ∀ n : ℕ, 2 < n →
      OeisA70823.a n ≡ 0 [MOD 3] ∧
        ∃ j k s : ℕ, OeisA70823.a n = 2 ^ j * 3 ^ k * s ∧ Squarefree s := by
  constructor
  · intro h
    exact h.elim
  · intro h
    obtain ⟨j, k, s, heq, hsf⟩ := (h 20 (by norm_num)).2
    have hp13 : (13 : ℕ).Prime := by decide
    have h169 : (13 : ℕ) * 13 ∣ OeisA70823.a 20 := by decide
    rw [heq] at h169
    have h1 : (13 : ℕ) ∣ 2 ^ j * 3 ^ k * s := (dvd_mul_right 13 13).trans h169
    rcases (hp13.dvd_mul).mp h1 with hA | hB
    · rcases (hp13.dvd_mul).mp hA with h2j | h3k
      · exact absurd (hp13.dvd_of_dvd_pow h2j) (by decide)
      · exact absurd (hp13.dvd_of_dvd_pow h3k) (by decide)
    · obtain ⟨t, rfl⟩ := hB
      have h2 : (13 : ℕ) ∣ 2 ^ j * 3 ^ k * t := by
        apply Nat.dvd_of_mul_dvd_mul_left (k := 13) (by norm_num)
        rw [show 13 * (2 ^ j * 3 ^ k * t) = 2 ^ j * 3 ^ k * (13 * t) from by ring]
        exact h169
      rcases (hp13.dvd_mul).mp h2 with hA2 | hB2
      · rcases (hp13.dvd_mul).mp hA2 with h2j | h3k
        · exact absurd (hp13.dvd_of_dvd_pow h2j) (by decide)
        · exact absurd (hp13.dvd_of_dvd_pow h3k) (by decide)
      · obtain ⟨u, rfl⟩ := hB2
        exact absurd ((Nat.squarefree_iff_prime_squarefree.mp hsf) 13 hp13 ⟨u, by ring⟩) (by decide)
