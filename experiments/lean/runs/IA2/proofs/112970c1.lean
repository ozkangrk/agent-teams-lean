import FormalConjectures.OEIS.«112970»
set_option maxRecDepth 10000

private lemma a_odd {m : ℕ} (hm : 1 ≤ m) : OeisA112970.a (2 * m + 1) = OeisA112970.a m := by
  conv_lhs =>
    unfold OeisA112970.a
  simp only []
  rw [if_neg (by omega : ¬ (2 * m + 1 = 0)), if_neg (by omega : ¬ (2 * m + 1 = 1)),
    if_pos (by omega : (2 * m + 1) % 2 = 1)]
  congr 1
  omega

theorem swarm_proof : type_of% @OeisA112970.conjecture1 := by
  intro n
  have h2 : (2:ℕ) ^ (n + 1) + 1 = 2 * 2 ^ n + 1 := by ring
  rw [h2, a_odd (by exact Nat.one_le_two_pow)]
