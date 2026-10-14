import FormalConjectures.OEIS.«112970»

open OeisA112970

private lemma odd_step (k : ℕ) : a (2 * k + 1) = a k := by
  match k with
  | 0 =>
    have he : 2 * 0 + 1 = 1 := by omega
    rw [he, a_1, a_0]
  | k + 1 =>
    have h0 : ¬ (2 * (k + 1) + 1 = 0) := by omega
    have h1 : ¬ (2 * (k + 1) + 1 = 1) := by omega
    have ho : (2 * (k + 1) + 1) % 2 = 1 := by omega
    have hd : (2 * (k + 1) + 1) / 2 = k + 1 := by omega
    conv_lhs => unfold a
    rw [if_neg h0, if_neg h1, if_pos ho, hd]

private lemma left_one (n : ℕ) : a (2^n - 1) = 1 := by
  induction n with
  | zero =>
    have hz : 2^(0:ℕ) - 1 = 0 := by norm_num
    rw [hz]
    exact a_0
  | succ n ih =>
    have hp : 2^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    have hpos : 0 < 2^n := by positivity
    have h : 2^(n+1) - 1 = 2 * (2^n - 1) + 1 := by rw [hp]; omega
    rw [h, odd_step]
    exact ih

private lemma right_one (n : ℕ) : a (3 * 2^n - 1) = 1 := by
  induction n with
  | zero =>
    have hz : 3 * 2^(0:ℕ) - 1 = 2 := by norm_num
    rw [hz]
    exact a_2
  | succ n ih =>
    have hp : 3 * 2^(n+1) = 2 * (3 * 2^n) := by rw [pow_succ]; ring
    have hpos : 0 < 3 * 2^n := by positivity
    have h : 3 * 2^(n+1) - 1 = 2 * (3 * 2^n - 1) + 1 := by rw [hp]; omega
    rw [h, odd_step]
    exact ih

theorem swarm_proof : ∀ (n : ℕ), a (2^n - 1) = a (3 * 2^n - 1) := by
  intro n
  rw [left_one n, right_one n]
