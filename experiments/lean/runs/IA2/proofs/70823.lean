import FormalConjectures.OEIS.«70823»

set_option maxHeartbeats 1000000000
set_option maxRecDepth 200000

private theorem p13 : Nat.Prime 13 := by decide

theorem swarm_proof : type_of% @OeisA70823.conjecture := by
  constructor
  · intro hf; exact hf.elim
  · intro hp
    have h20 := (hp 20 (by norm_num)).2
    obtain ⟨j, k, s, hs, hsf⟩ := h20
    have hd : (13 * 13 : ℕ) ∣ OeisA70823.a 20 := by decide
    rw [hs] at hd
    have hc : Nat.Coprime (13 * 13) (2 ^ j * 3 ^ k) := by
      rw [show 13 * 13 = 13 ^ 2 from by ring, Nat.coprime_pow_left_iff (by norm_num),
        Nat.Prime.coprime_iff_not_dvd p13]
      intro h13
      rcases (Nat.Prime.dvd_mul p13).mp h13 with h | h
      · exact absurd (Nat.Prime.dvd_of_dvd_pow p13 h) (by decide)
      · exact absurd (Nat.Prime.dvd_of_dvd_pow p13 h) (by decide)
    have h169 : (13 * 13 : ℕ) ∣ s := Nat.Coprime.dvd_of_dvd_mul_left hc hd
    have hu := hsf 13 h169
    have h1 : (13 : ℕ) = 1 := Nat.isUnit_iff.mp hu
    norm_num at h1
