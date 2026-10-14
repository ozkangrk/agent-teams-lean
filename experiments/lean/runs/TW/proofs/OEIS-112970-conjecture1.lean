import FormalConjectures.OEIS.«112970»

open OeisA112970

private lemma a_step (m : ℕ) (h0 : m ≠ 0) (h1 : m ≠ 1) (ho : m % 2 = 1) :
    a m = a (m / 2) := by
  conv_lhs => unfold a
  rw [if_neg h0, if_neg h1, if_pos ho]

theorem swarm_proof : ∀ (n : ℕ), a (2^n) = a (2^(n + 1) + 1) := by
  intro n
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hp2 : (2 ^ (n + 1)) % 2 = 0 := by
    rw [hpow, Nat.mul_mod_right]
  have hpos : 0 < 2 ^ (n + 1) := by positivity
  have hkey : a (2 ^ (n + 1) + 1) = a (2 ^ n) := by
    rw [a_step (2 ^ (n + 1) + 1) (by omega) (by omega) (by omega)]
    have hd : (2 ^ (n + 1) + 1) / 2 = 2 ^ n := by omega
    rw [hd]
  rw [hkey]
