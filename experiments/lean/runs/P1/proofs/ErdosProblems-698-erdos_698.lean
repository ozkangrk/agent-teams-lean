import FormalConjectures.ErdosProblems.«698»

/-!
Infrastructure toward Erdős 698 (Erdős–Szemerédi minimum-gcd conjecture).

Decomposition of the problem:

* `Erdos698Aux.vandermonde` : the identity
  `C(n,i) * C(n-i,j-i) = C(n,j) * C(j,i)` (proved).
* `Erdos698Aux.es_bound` : the Erdős–Szekeres bound
  `C(n,i) ≤ C(j,i) * gcd(C(n,i), C(n,j))`, i.e. `gcd ≥ C(n,i)/C(j,i)` (proved).
* `Erdos698Aux.aux` : `i^2*(i-1) ≤ 4^i` for `i ≥ 2` (proved).
* `Erdos698Aux.bergman_core` : the remaining analytic content from Bergman [Be11],
  stated over ℕ as `2^(2i) * n < 16 * i^2 * (i-1) * gcd^2`, i.e.
  `gcd > 2^i * √n / (4*i*√(i-1))` — the single remaining `sorry`.
  (This is the explicit bound of the public Lean proof cited upstream.)
* `Erdos698Aux.h_le_gcd` : `bergman_core` + `aux` give `⌊√n⌋ / 4 ≤ gcd` (proved,
  modulo `bergman_core`).

With `bergman_core` admitted, `swarm_proof` below closes the problem with
`h n = ⌊√n⌋ / 4`.
-/

open Filter Erdos698

namespace Erdos698Aux

/-- Vandermonde-type identity for binomial coefficients. -/
theorem vandermonde (n i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    n.choose i * (n - i).choose (j - i) = n.choose j * j.choose i := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (hij.trans hjn)
  have e2 := Nat.choose_mul_factorial_mul_factorial (by omega : j - i ≤ n - i)
  have e3 := Nat.choose_mul_factorial_mul_factorial hij
  have e4 := Nat.choose_mul_factorial_mul_factorial hjn
  rw [show n - i - (j - i) = n - j by omega] at e2
  have e2b : (n - i).choose (j - i) * (Nat.factorial (j - i) * Nat.factorial (n - j))
      = Nat.factorial (n - i) := by rw [Nat.mul_assoc] at e2; exact e2
  have e3b : j.choose i * (Nat.factorial i * Nat.factorial (j - i))
      = Nat.factorial j := by rw [Nat.mul_assoc] at e3; exact e3
  have hK : 0 < Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.mul_pos (Nat.factorial_pos _)
      (Nat.factorial_pos _))
  have L : n.choose i * ((n - i).choose (j - i)
        * (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j))))
      = Nat.factorial n := by
    calc n.choose i * ((n - i).choose (j - i)
          * (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j))))
        = (n.choose i * Nat.factorial i)
          * ((n - i).choose (j - i)
            * (Nat.factorial (j - i) * Nat.factorial (n - j))) := by ring
      _ = (n.choose i * Nat.factorial i) * Nat.factorial (n - i) := by rw [e2b]
      _ = Nat.factorial n := e1
  have R : n.choose j * (j.choose i
        * (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j))))
      = Nat.factorial n := by
    calc n.choose j * (j.choose i
          * (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j))))
        = (n.choose j * (j.choose i * (Nat.factorial i * Nat.factorial (j - i))))
          * Nat.factorial (n - j) := by ring
      _ = (n.choose j * Nat.factorial j) * Nat.factorial (n - j) := by rw [e3b]
      _ = Nat.factorial n := e4
  refine Nat.eq_of_mul_eq_mul_right hK ?_
  calc (n.choose i * (n - i).choose (j - i))
        * (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)))
      = n.choose i * ((n - i).choose (j - i)
          * (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)))) := by
          rw [Nat.mul_assoc]
    _ = Nat.factorial n := L
    _ = n.choose j * (j.choose i
          * (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j)))) := R.symm
    _ = (n.choose j * j.choose i)
        * (Nat.factorial i * (Nat.factorial (j - i) * Nat.factorial (n - j))) := by
          rw [← Nat.mul_assoc]

/-- Erdős–Szekeres: `gcd(C(n,i), C(n,j)) ≥ C(n,i)/C(j,i)`, as a ℕ inequality. -/
theorem es_bound (n i j : ℕ) (hij : i < j) (hjn : j ≤ n) :
    n.choose i ≤ j.choose i * Nat.gcd (n.choose i) (n.choose j) := by
  have hiden := vandermonde n i j (Nat.le_of_lt hij) hjn
  have hu0 : 0 < n.choose i := Nat.choose_pos (by omega)
  have hg0 : 0 < Nat.gcd (n.choose i) (n.choose j) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hu0
  have ht0 : 0 < j.choose i := Nat.choose_pos (Nat.le_of_lt hij)
  have hd1 : n.choose i = Nat.gcd (n.choose i) (n.choose j)
      * (n.choose i / Nat.gcd (n.choose i) (n.choose j)) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hd2 : n.choose j = Nat.gcd (n.choose i) (n.choose j)
      * (n.choose j / Nat.gcd (n.choose i) (n.choose j)) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  have heq : Nat.gcd (n.choose i) (n.choose j)
        * ((n.choose i / Nat.gcd (n.choose i) (n.choose j)) * (n - i).choose (j - i))
      = Nat.gcd (n.choose i) (n.choose j)
        * ((n.choose j / Nat.gcd (n.choose i) (n.choose j)) * j.choose i) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← hd1, ← hd2]
    exact hiden
  have hcancel : (n.choose i / Nat.gcd (n.choose i) (n.choose j))
      * (n - i).choose (j - i)
      = (n.choose j / Nat.gcd (n.choose i) (n.choose j)) * j.choose i :=
    Nat.mul_left_cancel hg0 heq
  have hcopr : (n.choose i / Nat.gcd (n.choose i) (n.choose j)).Coprime
      (n.choose j / Nat.gcd (n.choose i) (n.choose j)) :=
    Nat.coprime_div_gcd_div_gcd hg0
  have hdvd : (n.choose i / Nat.gcd (n.choose i) (n.choose j)) ∣ j.choose i :=
    hcopr.dvd_of_dvd_mul_right
      ⟨(n - i).choose (j - i), by rw [Nat.mul_comm (j.choose i)]; exact hcancel.symm⟩
  calc n.choose i
      = Nat.gcd (n.choose i) (n.choose j)
        * (n.choose i / Nat.gcd (n.choose i) (n.choose j)) := hd1
    _ ≤ Nat.gcd (n.choose i) (n.choose j) * j.choose i :=
        Nat.mul_le_mul_left _ (Nat.le_of_dvd ht0 hdvd)
    _ = j.choose i * Nat.gcd (n.choose i) (n.choose j) := Nat.mul_comm _ _

/-- Family-B divisibility: for a prime `p` with `2p ≤ n < 3p` and `n < p^2`
(i.e. `n/3 < p ≤ n/2`), one has `p ∣ C(n,k)` exactly in the window
`n - 2p < k < p` (Kummer: a single carry mod `p`). Positive direction here. -/
theorem prime_dvd_choose_of_lt_three_mul {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (h2p : 2 * p ≤ n) (h3n : n < 3 * p) (hnp2 : n < p * p)
    (hk : n - 2 * p < k) (hkp : k < p) : p ∣ n.choose k := by
  have hn0 : n ≠ 0 := by omega
  have hr : n - 2 * p < p := by omega
  have hs : p + (n - 2 * p) - k < p := by omega
  have hs0 : 0 < p + (n - 2 * p) - k := by omega
  have hsplit : n - k = p + (p + (n - 2 * p) - k) := by omega
  have hmodn : (n - k) % p = p + (n - 2 * p) - k := by
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt hs]
  have hmodk : k % p = k := Nat.mod_eq_of_lt hkp
  have hfc := Nat.factorization_choose hp hkn
    (Nat.log_lt_of_lt_pow hn0 (by rw [Nat.pow_two]; exact hnp2))
  have hmem : 1 ∈ Finset.filter (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)
      (Finset.Ico 1 2) := by
    refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · exact Finset.mem_Ico.2 (by omega)
    · simp only [pow_one, hmodk, hmodn]
      omega
  have hcard : 0 < (Finset.filter (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)
      (Finset.Ico 1 2)).card := Finset.card_pos.2 ⟨1, hmem⟩
  exact Nat.dvd_of_factorization_pos (by rw [hfc]; omega)

/-- Family-B zero direction: same regime (`2p ≤ n < 3p`, `n < p^2`), but
`k ≤ n - 2p`: then `p ∤ C(n,k)` (no carry mod `p`). -/
theorem prime_not_dvd_choose_of_lt_three_mul {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (h2p : 2 * p ≤ n) (h3n : n < 3 * p) (hnp2 : n < p * p)
    (hk : k ≤ n - 2 * p) : ¬ p ∣ n.choose k := by
  have hn0 : n ≠ 0 := by omega
  have hr : n - 2 * p < p := by omega
  have hkp : k < p := Nat.lt_of_le_of_lt hk hr
  have hmodk : k % p = k := Nat.mod_eq_of_lt hkp
  have hmodn : (n - k) % p = n - 2 * p - k := by
    have hsplit : n - k = p * 2 + (n - 2 * p - k) := by omega
    rw [hsplit, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  have hfc := Nat.factorization_choose hp hkn
    (Nat.log_lt_of_lt_pow hn0 (by rw [Nat.pow_two]; exact hnp2))
  have hempty : (Finset.filter (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)
      (Finset.Ico 1 2)) = (∅ : Finset ℕ) := by
    ext x
    by_cases hx : x = 1
    · subst hx
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_Ico] at h
        obtain ⟨_, h3⟩ := h
        simp only [pow_one, hmodk, hmodn] at h3
        omega
      · intro h
        simp at h
    · constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_Ico] at h
        obtain ⟨⟨h1, h2⟩, _⟩ := h
        omega
      · intro h
        simp at h
  have hzero : (n.choose k).factorization p = 0 := by
    rw [hfc, hempty, Finset.card_empty]
  intro hdvd
  exact absurd (hp.factorization_pos_of_dvd (Nat.ne_of_gt (Nat.choose_pos hkn)) hdvd)
    (by rw [hzero]; omega)

/-- Family-B zero direction, second window: same regime (`2p ≤ n < 3p`, `n < p²`)
with `p ≤ k ≤ n/2`: then `p ∤ C(n,k)`. -/
theorem prime_not_dvd_choose_of_ge_of_lt_three_mul {p n k : ℕ} (hp : p.Prime)
    (hk2 : k ≤ n / 2) (h2p : 2 * p ≤ n) (h3n : n < 3 * p) (hnp2 : n < p * p)
    (hk : p ≤ k) : ¬ p ∣ n.choose k := by
  have hn0 : n ≠ 0 := by omega
  have hkn : k ≤ n := by omega
  have hr : n - 2 * p < p := by omega
  have hk2p : k < 2 * p := by omega
  have hq : k - p ≤ n - 2 * p := by omega
  have hmodk : k % p = k - p := by
    have hsplit : k = p + (k - p) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmodn : (n - k) % p = n - 2 * p - (k - p) := by
    have hsplit : n - k = p + (n - 2 * p - (k - p)) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hfc := Nat.factorization_choose hp hkn
    (Nat.log_lt_of_lt_pow hn0 (by rw [Nat.pow_two]; exact hnp2))
  have hempty : (Finset.filter (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)
      (Finset.Ico 1 2)) = (∅ : Finset ℕ) := by
    ext x
    by_cases hx : x = 1
    · subst hx
      constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_Ico] at h
        obtain ⟨_, h3⟩ := h
        simp only [pow_one, hmodk, hmodn] at h3
        omega
      · intro h
        simp at h
    · constructor
      · intro h
        simp only [Finset.mem_filter, Finset.mem_Ico] at h
        obtain ⟨⟨h1, h2⟩, _⟩ := h
        omega
      · intro h
        simp at h
  have hzero : (n.choose k).factorization p = 0 := by
    rw [hfc, hempty, Finset.card_empty]
  intro hdvd
  exact absurd (hp.factorization_pos_of_dvd (Nat.ne_of_gt (Nat.choose_pos hkn)) hdvd)
    (by rw [hzero]; omega)

/-- Family-B exact criterion in the problem's range `k ≤ n/2`: for `2p ≤ n < 3p`, `n < p²`,
one has `p ∣ C(n,k)` iff `n - 2p < k < p`. -/
theorem prime_iff_dvd_choose_of_lt_three_mul {p n k : ℕ} (hp : p.Prime)
    (hk2 : k ≤ n / 2) (h2p : 2 * p ≤ n) (h3n : n < 3 * p) (hnp2 : n < p * p) :
    p ∣ n.choose k ↔ n - 2 * p < k ∧ k < p := by
  have hkn : k ≤ n := by omega
  constructor
  · intro hdvd
    by_cases hk : k ≤ n - 2 * p
    · exact absurd hdvd
        (prime_not_dvd_choose_of_lt_three_mul hp hkn h2p h3n hnp2 hk)
    · by_cases hkp : p ≤ k
      · exact absurd hdvd
          (prime_not_dvd_choose_of_ge_of_lt_three_mul hp hk2 h2p h3n hnp2 hkp)
      · exact ⟨by omega, by omega⟩
  · intro ⟨h1, h2⟩
    exact prime_dvd_choose_of_lt_three_mul hp hkn h2p h3n hnp2 h1 h2

/-- `i^2 * (i-1) ≤ 4^i` for `i ≥ 2`, so `i * √(i-1) ≤ 2^i`. -/
theorem aux (i : ℕ) (hi : 2 ≤ i) : i * i * (i - 1) ≤ 2 ^ (2 * i) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk1 : 1 ≤ k := by omega
  rw [Nat.add_sub_cancel]
  clear hi hk1
  induction k with
  | zero => norm_num
  | succ m ih =>
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m <;> norm_num
    · -- m ≥ 2
      have hmmm : 2 * 2 ≤ m * m := Nat.mul_le_mul hm2 hm2
      have h34 : 4 ≤ 3 * (m * m) := by nlinarith [hmmm]
      have hstep : (m + 1 + 1) * (m + 1 + 1) * (m + 1)
          ≤ 4 * ((m + 1) * (m + 1) * m) := by
        nlinarith [h34]
      have hexp : 2 ^ (2 * (m + 1 + 1)) = 4 * 2 ^ (2 * (m + 1)) := by
        rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by omega, pow_add, pow_two]
        ring
      rw [hexp]
      calc (m + 1 + 1) * (m + 1 + 1) * (m + 1)
          ≤ 4 * ((m + 1) * (m + 1) * m) := hstep
        _ ≤ 4 * 2 ^ (2 * (m + 1)) := Nat.mul_le_mul_left 4 ih

/-- Case A of `bergman_core`: when `2*j^2 ≤ n` the Erdős–Szekeres bound
`gcd ≥ C(n,i)/C(j,i)` alone suffices. -/
theorem bg_caseA (n i j : ℕ) (hi : 2 ≤ i) (hij : i < j) (hjn : j ≤ n)
    (hA : 2 * j * j ≤ n) :
    2 ^ (2 * i) * n < 16 * i * i * (i - 1) * Nat.gcd (n.choose i) (n.choose j) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hj0 : 0 < j := by omega
  have hterm : ∀ r ∈ Finset.range i, (j - r) * n ≤ (n - r) * j := by
    intro r _
    have hrj : r * j ≤ r * n := Nat.mul_le_mul_left _ hjn
    rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm n j]
    omega
  have hpr : Nat.factorial i * j.choose i * n ^ i
      ≤ Nat.factorial i * n.choose i * j ^ i := by
    have hc : (∏ r ∈ Finset.range i, (j - r)) * (∏ _ ∈ Finset.range i, n)
          ≤ (∏ r ∈ Finset.range i, (n - r)) * (∏ _ ∈ Finset.range i, j) := by
        calc (∏ r ∈ Finset.range i, (j - r)) * (∏ _ ∈ Finset.range i, n)
            = ∏ r ∈ Finset.range i, ((j - r) * n) := Finset.prod_mul_distrib.symm
          _ ≤ ∏ r ∈ Finset.range i, ((n - r) * j) :=
              Finset.prod_le_prod (fun r _ => Nat.zero_le ((j - r) * n)) hterm
          _ = (∏ r ∈ Finset.range i, (n - r)) * (∏ _ ∈ Finset.range i, j) :=
              Finset.prod_mul_distrib
    rw [← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose] at hc
    simpa [Finset.prod_const, Finset.card_range] using hc
  have hcj : 0 < j.choose i := Nat.choose_pos (by omega)
  have hb := es_bound n i j hij hjn
  set g := Nat.gcd (n.choose i) (n.choose j) with hgdef
  have hb' : Nat.factorial i * n.choose i ≤ Nat.factorial i * (j.choose i * g) :=
    Nat.mul_le_mul_left _ hb
  have hbig : Nat.factorial i * (j.choose i * n ^ i)
      ≤ Nat.factorial i * (j.choose i * (g * j ^ i)) := by
    calc Nat.factorial i * (j.choose i * n ^ i)
        = (Nat.factorial i * j.choose i) * n ^ i := by ring
      _ ≤ (Nat.factorial i * n.choose i) * j ^ i := hpr
      _ = Nat.factorial i * (n.choose i * j ^ i) := by ring
      _ ≤ Nat.factorial i * ((j.choose i * g) * j ^ i) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right (j ^ i) hb)
      _ = Nat.factorial i * (j.choose i * (g * j ^ i)) := by ring
  have hcx : j.choose i * n ^ i ≤ j.choose i * (g * j ^ i) :=
    Nat.le_of_mul_le_mul_left hbig (Nat.factorial_pos _)
  have hn : n ^ i ≤ g * j ^ i := Nat.le_of_mul_le_mul_left hcx hcj
  have hni : 0 < n ^ i := Nat.pow_pos hn0
  have h2 : n ^ i * n ^ i ≤ g * g * (j ^ i * j ^ i) := by
    calc n ^ i * n ^ i ≤ (g * j ^ i) * (g * j ^ i) := Nat.mul_le_mul hn hn
      _ = g * g * (j ^ i * j ^ i) := by ring
  have hii : 2 * 2 ≤ i * i := Nat.mul_le_mul hi hi
  have hi1 : 1 ≤ i - 1 := by omega
  have hm : (2 * 2) * 1 ≤ (i * i) * (i - 1) := Nat.mul_le_mul hii hi1
  have hC : 16 * ((2 * 2) * 1) ≤ 16 * ((i * i) * (i - 1)) := Nat.mul_le_mul_left _ hm
  have hp2j : 2 ^ i * (j ^ i * j ^ i) ≤ n ^ i := by
    have hp : (2 * j * j) ^ i ≤ n ^ i := Nat.pow_le_pow_left hA i
    rw [Nat.mul_pow, Nat.mul_pow] at hp
    ring_nf at hp ⊢
    linarith
  have he : 2 ^ i = 2 * 2 ^ (i - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    subst hk
    simp only [Nat.add_sub_cancel, Nat.pow_succ]
    ring
  have hnp : n ^ (i - 1) * n = n ^ i := by
    obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    subst hk
    simp only [Nat.add_sub_cancel, Nat.pow_succ]
  have hnle : n ≤ n ^ i := by
    calc n = n ^ 1 := (Nat.pow_one n).symm
      _ ≤ n ^ i := Nat.pow_le_pow_right (show (1:ℕ) ≤ n by omega) (show (1:ℕ) ≤ i by omega)
  have h21 : 2 ^ (i - 1) ≤ n ^ (i - 1) := Nat.pow_le_pow_left (by omega) (i - 1)
  have hAn : 2 ^ i * n < 16 * ((i * i) * (i - 1)) * n ^ i := by
    calc 2 ^ i * n = 2 * (2 ^ (i - 1) * n) := by rw [he]; ring
      _ ≤ 2 * (n ^ (i - 1) * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right n h21)
      _ = 2 * n ^ i := by rw [hnp]
      _ < 16 * ((2 * 2) * 1) * n ^ i := by nlinarith [hni]
      _ ≤ 16 * ((i * i) * (i - 1)) * n ^ i := Nat.mul_le_mul_right (n ^ i) hC
  have hst : (2 ^ i * n) * n ^ i < (16 * ((i * i) * (i - 1)) * n ^ i) * n ^ i :=
    (Nat.mul_lt_mul_right hni).2 hAn
  have hnB : n * (2 ^ i * (j ^ i * j ^ i)) ≤ n * n ^ i :=
    Nat.mul_le_mul_left _ hp2j
  have hBB : n * n ^ i ≤ n ^ i * n ^ i := Nat.mul_le_mul_right (n ^ i) hnle
  have hC2 : 16 * ((i * i) * (i - 1)) * (n ^ i * n ^ i)
      ≤ 16 * ((i * i) * (i - 1)) * (g * g * (j ^ i * j ^ i)) :=
    Nat.mul_le_mul_left _ h2
  have e1 : 2 ^ i * (n * (2 ^ i * (j ^ i * j ^ i))) ≤ 2 ^ i * (n * n ^ i) :=
    Nat.mul_le_mul_left _ hnB
  have e2 : 2 ^ i * (n * n ^ i) ≤ 2 ^ i * (n ^ i * n ^ i) :=
    Nat.mul_le_mul_left _ hBB
  have hfin : (2 ^ (2 * i) * n) * (j ^ i * j ^ i)
      < (16 * i * i * (i - 1) * (g * g)) * (j ^ i * j ^ i) := by
    rw [show 2 ^ (2 * i) = 2 ^ i * 2 ^ i by
      rw [Nat.mul_comm 2 i, Nat.pow_mul, Nat.pow_two]]
    nlinarith [hst, e1, e2, hC2]
  rw [Nat.pow_two]
  exact Nat.lt_of_mul_lt_mul_right hfin

/-- Exact factorization: with `g = gcd(C(n,i), C(n,j))` there is a common factor `D`
such that `C(n,i) * D = g * C(j,i)` and `C(n,j) * D = g * C(n-i,j-i)`.
(In rational form: `g = C(n,i) * D / C(j,i)` with `D = gcd(C(j,i), C(n-i,j-i))`.) -/
theorem gcd_decomp (n i j : ℕ) (hij : i < j) (hjn : j ≤ n) :
    ∃ D : ℕ, n.choose i * D = Nat.gcd (n.choose i) (n.choose j) * j.choose i
      ∧ n.choose j * D = Nat.gcd (n.choose i) (n.choose j) * (n - i).choose (j - i) := by
  have hiden : n.choose i * (n - i).choose (j - i) = n.choose j * j.choose i :=
    vandermonde n i j (Nat.le_of_lt hij) hjn
  have hu0 : 0 < n.choose i := Nat.choose_pos (by omega)
  have hv0 : 0 < n.choose j := Nat.choose_pos hjn
  have hg0 : 0 < Nat.gcd (n.choose i) (n.choose j) :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hu0
  have hd1 : n.choose i = Nat.gcd (n.choose i) (n.choose j)
      * (n.choose i / Nat.gcd (n.choose i) (n.choose j)) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  have hd2 : n.choose j = Nat.gcd (n.choose i) (n.choose j)
      * (n.choose j / Nat.gcd (n.choose i) (n.choose j)) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  set g := Nat.gcd (n.choose i) (n.choose j) with hgdef
  set u₁ := n.choose i / g with hu₁def
  set v₁ := n.choose j / g with hv₁def
  have hpos₁ : 0 < u₁ := Nat.pos_of_dvd_of_pos ⟨g, hd1.trans (Nat.mul_comm g u₁)⟩ hu0
  have hpos₁' : 0 < v₁ := Nat.pos_of_dvd_of_pos ⟨g, hd2.trans (Nat.mul_comm g v₁)⟩ hv0
  rw [hd1, hd2, Nat.mul_assoc, Nat.mul_assoc] at hiden
  have hcancel : u₁ * (n - i).choose (j - i) = v₁ * j.choose i :=
    Nat.mul_left_cancel hg0 hiden
  have hcopr : u₁.Coprime v₁ := Nat.coprime_div_gcd_div_gcd hg0
  have hdvdt : u₁ ∣ j.choose i :=
    hcopr.dvd_of_dvd_mul_right
      ⟨(n - i).choose (j - i), by rw [Nat.mul_comm]; exact hcancel.symm⟩
  have hdvdw : v₁ ∣ (n - i).choose (j - i) :=
    hcopr.symm.dvd_of_dvd_mul_left ⟨j.choose i, hcancel⟩
  obtain ⟨c, hc⟩ := hdvdt
  obtain ⟨e, he⟩ := hdvdw
  have hsub : u₁ * (v₁ * e) = v₁ * (u₁ * c) := by rw [← he, ← hc]; exact hcancel
  have hrw : v₁ * (u₁ * c) = u₁ * (v₁ * c) := Nat.mul_left_comm v₁ u₁ c
  have hce : c = e :=
    Nat.mul_left_cancel hpos₁'
      (Nat.mul_left_cancel hpos₁
        (hsub.trans hrw).symm)
  refine ⟨c, ?_, ?_⟩
  · rw [hc, hd1]; ring
  · rw [he, ← hce, hd2]; ring

/-- If a prime `p` divides `n` but not `k` (with `0 < k < n`), then `p ∣ C(n,k)` (Lucas). -/
theorem prime_dvd_choose {p : ℕ} (hp : p.Prime) {n k : ℕ} (hpn : p ∣ n)
    (hk0 : 0 < k) (hkn : k < n) (hkp : ¬ p ∣ k) : p ∣ n.choose k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : n < 2 ^ (n + 1) := by
    clear hpn hkn
    induction n with
    | zero => norm_num
    | succ k ih =>
        have hXpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos _
        rw [Nat.pow_succ]
        calc k + 1 ≤ 2 ^ (k + 1) := Nat.succ_le_of_lt ih
          _ < 2 ^ (k + 1) * 2 := by omega
  have hp2 : 2 ^ (n + 1) ≤ p ^ (n + 1) := by gcongr; exact hp.two_le
  have hlt1 : n < p ^ (n + 1) := lt_of_lt_of_le h2 hp2
  have hlt2 : k < p ^ (n + 1) := lt_of_le_of_lt (Nat.le_of_lt hkn) hlt1
  have hlucas := Choose.choose_modEq_prod_range_choose_nat hlt1 hlt2
  have hkp' : 0 < k % p :=
    Nat.pos_of_ne_zero (fun h => hkp (Nat.dvd_iff_mod_eq_zero.2 h))
  have hzero : (∏ i ∈ Finset.range (n + 1),
      Nat.choose (n / p ^ i % p) (k / p ^ i % p)) = 0 := by
    have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    refine Finset.prod_eq_zero hmem ?_
    simp only [pow_zero, Nat.div_one]
    rw [Nat.dvd_iff_mod_eq_zero.1 hpn]
    exact Nat.choose_eq_zero_of_lt hkp'
  rw [Nat.ModEq, hzero, Nat.zero_mod] at hlucas
  exact Nat.dvd_iff_mod_eq_zero.2 hlucas

/-- The remaining analytic content (Bergman [Be11]):
`gcd > 2^i * √n / (4 * i * √(i-1))` for `2 ≤ i < j ≤ n/2`. -/
theorem bergman_core (n i j : ℕ) (hi : 2 ≤ i) (hij : i < j) (hj : j ≤ n / 2) :
    2 ^ (2 * i) * n < 16 * i * i * (i - 1) * Nat.gcd (n.choose i) (n.choose j) ^ 2 := by
  rcases Nat.lt_or_ge n (2 * j * j) with hB | hA
  · -- Case B (`2 * j * j > n`): the analytic core of Bergman [Be11] — open.
    sorry
  · exact bg_caseA n i j hi hij (by omega) hA

/-- The witnessing function `h n = ⌊√n⌋ / 4`. -/
def hfun : ℕ → ℕ := fun n => Nat.sqrt n / 4

theorem tendsto_hfun : Tendsto hfun atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨(4 * b + 1) ^ 2, fun n hn => ?_⟩
  have h41 : (4 * b) ^ 2 ≤ (4 * b + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.le_add_right _ 1) 2
  have h4 : 4 * b ≤ Nat.sqrt n := Nat.le_sqrt'.2 (le_trans h41 hn)
  show b ≤ Nat.sqrt n / 4
  omega

theorem h_le_gcd (n i j : ℕ) (hi : 2 ≤ i) (hij : i < j) (hj : j ≤ n / 2) :
    Nat.sqrt n / 4 ≤ Nat.gcd (n.choose i) (n.choose j) := by
  have hc := bergman_core n i j hi hij hj
  have ha := aux i hi
  set g := Nat.gcd (n.choose i) (n.choose j) with hgdef
  have hpos : 0 < i * i * (i - 1) := by
    have h1 : 1 ≤ i - 1 := by omega
    have h2 : 2 * 2 ≤ i * i := Nat.mul_le_mul hi hi
    have h3 : 2 * 1 ≤ i * (i - 1) := Nat.mul_le_mul hi h1
    have : 4 ≤ (i * i) * (i - 1) := Nat.mul_le_mul h2 h1
    omega
  have key : i * i * (i - 1) * n < i * i * (i - 1) * (16 * g * g) := by
    calc i * i * (i - 1) * n ≤ 2 ^ (2 * i) * n := Nat.mul_le_mul_right n ha
      _ < 16 * i * i * (i - 1) * g ^ 2 := hc
      _ = i * i * (i - 1) * (16 * g * g) := by ring
  have h16 : n < 16 * g * g := Nat.lt_of_mul_lt_mul_left key
  have hs : Nat.sqrt n < 4 * g := by
    rw [Nat.sqrt_lt', Nat.pow_two]
    nlinarith [h16]
  omega

end Erdos698Aux

theorem swarm_proof : answer(True) ↔
    ∃ h : ℕ → ℕ, Tendsto h atTop atTop ∧
      ∀ n i j : ℕ, 2 ≤ i → i < j → j ≤ n / 2 →
        h n ≤ Nat.gcd (n.choose i) (n.choose j) := by
  constructor
  · intro _
    exact ⟨Erdos698Aux.hfun, Erdos698Aux.tendsto_hfun,
      fun n i j hi hij hj => Erdos698Aux.h_le_gcd n i j hi hij hj⟩
  · intro _
    trivial
