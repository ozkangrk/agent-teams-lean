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

private lemma a1 : OeisA112970.a 0 = 1 := by unfold OeisA112970.a; rfl
private lemma a2 : OeisA112970.a 1 = 1 := by unfold OeisA112970.a; rfl
private lemma a3 : OeisA112970.a 2 = 1 := by unfold OeisA112970.a; unfold OeisA112970.a; unfold OeisA112970.a; rfl

theorem swarm_proof : type_of% @OeisA112970.conjecture2 := by
  intro n
  induction n with
  | zero =>
    show OeisA112970.a ((2:ℕ)^0 - 1) = OeisA112970.a (3 * (2:ℕ)^0 - 1)
    have h0 : ((2:ℕ)^0 - 1) = 0 := by norm_num
    have h2v : 3 * (2:ℕ)^0 - 1 = 2 := by norm_num
    rw [h0, h2v, a1, a3]
  | succ n ih =>
    have h2 : (2:ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 : (2:ℕ)^(0+1) - 1 = 1 := by norm_num
      have h5 : 3 * (2:ℕ)^(0+1) - 1 = 5 := by norm_num
      rw [h1, h5, show (5:ℕ) = 2 * 2 + 1 from rfl, a_odd (by norm_num), a2, a3]
    · have hp : 2 ≤ (2:ℕ)^n := by
        induction n with
        | zero => omega
        | succ m ih => rw [show (2:ℕ)^(m+1) = 2*2^m from by ring]
                       exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos m)
      have hpos : 0 < (2:ℕ)^n := Nat.two_pow_pos n
      rw [h2,
        show 2 * (2:ℕ)^n - 1 = 2 * ((2:ℕ)^n - 1) + 1 from by omega,
        show 3 * (2 * (2:ℕ)^n) - 1 = 2 * ((3:ℕ) * 2^n - 1) + 1 from by omega]
      rw [a_odd (by omega : 1 ≤ (2:ℕ)^n - 1), a_odd (by omega)]
      exact ih
