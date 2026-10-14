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

private lemma cone_one (n : ℕ) : a (2^n - 1) = 1 := by
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

private lemma even_step (k : ℕ) (hk : 2 ≤ k) : a (2 * k) = a k + a (k - 2) := by
  have hne0 : ¬ (2 * k = 0) := by omega
  have hne1 : ¬ (2 * k = 1) := by omega
  have hp : ¬ ((2 * k) % 2 = 1) := by omega
  have hd : (2 * k) / 2 = k := by omega
  have hk2 : ¬ (k < 2) := by omega
  conv_lhs => unfold a
  rw [if_neg hne0, if_neg hne1, if_neg hp]
  simp only [hd, if_neg hk2]

private lemma Shalf (m : ℕ) : a (2^(m+1) - 2) = (m+2) / 2 := by
  induction m using Nat.twoStepInduction with
  | zero =>
    have hz : 2^(0+1) - 2 = 0 := by norm_num
    rw [hz]
    exact a_0
  | one =>
    have hz : 2^(1+1) - 2 = 2 := by norm_num
    rw [hz]
    exact a_2
  | more k ih1 ih2 =>
    have e : (k+2)+1 = k+3 := by omega
    rw [e]
    have hp : 2^(k+3) = 2 * 2^(k+2) := by rw [pow_succ]; ring
    have hp4 : 4 ≤ 2^(k+2) := by
      have h2 : 2^(k+2) = 4 * 2^k := by rw [pow_add]; ring
      have h0 : 0 < 2^k := by positivity
      omega
    have hev : 2^(k+3) - 2 = 2 * (2^(k+2) - 1) := by rw [hp]; omega
    rw [hev, even_step (2^(k+2) - 1) (by omega)]
    rw [cone_one (k+2)]
    have hp2 : 2^(k+2) = 2 * 2^(k+1) := by rw [pow_succ]; ring
    have hp1 : 2^(k+1) = 2 * 2^k := by rw [pow_succ]; ring
    have hposk : 0 < 2^k := by positivity
    have ho : 2^(k+2) - 1 - 2 = 2 * (2^(k+1) - 2) + 1 := by omega
    rw [ho, odd_step (2^(k+1) - 2), ih1]
    omega

private lemma arith (m : ℕ) : m ^ 2 / 4 + (m+1) / 2 = (m+1) ^ 2 / 4 := by
  rw [Nat.pow_two, Nat.pow_two]
  cases Nat.mod_two_eq_zero_or_one m with
  | inl h =>
    obtain ⟨r, hr⟩ : ∃ r, m = 2 * r := ⟨m / 2, by omega⟩
    subst hr
    have h1 : (2*r)*(2*r) = 4*(r*r) := by ring
    have h2 : (2*r+1)*(2*r+1) = 4*(r*r+r) + 1 := by ring
    rw [h1, h2]
    omega
  | inr h =>
    obtain ⟨r, hr⟩ : ∃ r, m = 2 * r + 1 := ⟨m / 2, by omega⟩
    subst hr
    have h1 : (2*r+1)*(2*r+1) = 4*(r*r+r) + 1 := by ring
    have h2 : (2*r+2)*(2*r+2) = 4*(r*r + 2*r + 1) := by ring
    rw [h1, h2]
    omega

theorem swarm_proof : ∀ (n : ℕ), a (2^n) = n ^ 2 / 4 + 1 := by
  intro n
  induction n with
  | zero =>
    have hz : (2:ℕ)^(0:ℕ) = 1 := by norm_num
    rw [hz, a_1]
    norm_num
  | succ n ih =>
    cases n with
    | zero =>
      have hz : (2:ℕ)^(0+1) = 2 := by norm_num
      rw [hz, a_2]
      norm_num
    | succ n' =>
      have hp : 2^(n'+1+1) = 2 * 2^(n'+1) := by rw [pow_succ]; ring
      have hp1 : 2^(n'+1) = 2 * 2^n' := by rw [pow_succ]; ring
      have hpos : 0 < 2^n' := by positivity
      have h2le : 2 ≤ 2^(n'+1) := by omega
      rw [hp, even_step (2^(n'+1)) h2le, ih, Shalf n']
      have ar := arith (n'+1)
      omega
