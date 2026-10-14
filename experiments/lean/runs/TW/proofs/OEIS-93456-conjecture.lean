
import FormalConjectures.OEIS.«93456»

open OeisA93456

namespace SwarmA93456

private lemma sq_bound (q : ℕ) (hq : 23 ≤ q) : (q - 1) * (q - 3) ≥ 16 * q := by
  obtain ⟨c, hc⟩ : ∃ c, q = c + 23 := ⟨q - 23, by omega⟩
  rw [hc]
  have e1 : c + 23 - 1 = c + 22 := by omega
  have e2 : c + 23 - 3 = c + 20 := by omega
  rw [e1, e2]
  have ee : (c + 22) * (c + 20) = c * c + 42 * c + 440 := by ring
  rw [ee]
  omega

private lemma four_mul (a b : ℕ) : (2 * a) * (2 * b) = 4 * (a * b) := by ring

/-- For a prime `p ≥ 23`, let `n` be minimal with `2*p ≤ C(n,2)`.  Then `2*p` lies in
row `n-1` while row `n` contains no multiple of `p`, so `p` witnesses `a (n-1) ∣ a n`. -/
private theorem key (p : ℕ) (hprime : p.Prime) (h23 : 23 ≤ p) :
    ∃ n : ℕ, 1 < n ∧ 2 * p ≤ n * (n - 1) / 2 ∧ ¬ (a (n - 1) ∣ a n) := by
  have hex : ∃ m : ℕ, 4 ≤ m ∧ 2 * p ≤ m * (m - 1) / 2 := by
    refine ⟨2 * p + 2, by omega, ?_⟩
    have hsub : 2 * p + 2 - 1 = 2 * p + 1 := by omega
    rw [hsub]
    have hM : (2 * p + 2) * (2 * p + 1) = 2 * ((p + 1) * (2 * p + 1)) := by ring
    rw [hM]
    have hD2 : 2 * ((p + 1) * (2 * p + 1)) / 2 = (p + 1) * (2 * p + 1) := by omega
    rw [hD2]
    have hle : 1 * (2 * p + 1) ≤ (p + 1) * (2 * p + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨hn4, hnlow⟩ := Nat.find_spec hex
  -- minimality bound
  have hmin : (Nat.find hex - 1) * (Nat.find hex - 2) / 2 < 2 * p := by
    by_cases hn5 : 5 ≤ Nat.find hex
    · by_contra hcon
      push_neg at hcon
      have hsub4 : Nat.find hex - 1 - 1 = Nat.find hex - 2 := by omega
      have hmem : 4 ≤ Nat.find hex - 1 ∧
          2 * p ≤ (Nat.find hex - 1) * ((Nat.find hex - 1) - 1) / 2 := by
        refine ⟨by omega, ?_⟩
        rw [hsub4]
        omega
      have hsle := Nat.find_min' hex hmem
      omega
    · have h4 : Nat.find hex = 4 := by omega
      rw [h4]
      norm_num
      omega
  -- upper bound: 2 * n ≤ p
  have h2n : 2 * Nat.find hex ≤ p := by
    by_contra hcon
    push_neg at hcon
    have h1 : p - 1 ≤ 2 * (Nat.find hex - 1) := by omega
    have h2 : p - 3 ≤ 2 * (Nat.find hex - 2) := by omega
    have hA0 := Nat.mul_le_mul h1 h2
    rw [four_mul] at hA0
    have hA : (p - 1) * (p - 3) ≤ 4 * ((Nat.find hex - 1) * (Nat.find hex - 2)) := hA0
    have hE := sq_bound p h23
    omega
  -- the top of row n is below 3 * p
  have htop : (Nat.find hex + 1) * Nat.find hex / 2 < 3 * p := by
    have hsplit : (Nat.find hex + 1) * Nat.find hex
        = (Nat.find hex - 1) * (Nat.find hex - 2) + (4 * Nat.find hex - 2) := by
      obtain ⟨t, ht⟩ : ∃ t, Nat.find hex = t + 2 := ⟨Nat.find hex - 2, by omega⟩
      rw [ht]
      have s1 : t + 2 - 1 = t + 1 := by omega
      have s2 : t + 2 - 2 = t := by omega
      have s3 : 4 * (t + 2) - 2 = 4 * t + 6 := by omega
      rw [s1, s2, s3]
      ring
    omega
  refine ⟨Nat.find hex, by omega, hnlow, ?_⟩
  intro hdvd
  have h4 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  -- 2 * p is a composite member of row (n-1), so p ∣ a (n-1)
  have hrow : 2 * p ∈ (Finset.Icc (Nat.choose (Nat.find hex - 1) 2 + 1)
      (Nat.choose (Nat.find hex) 2)).filter (fun k => 1 < k ∧ ¬ k.Prime) := by
    have hA : Nat.choose (Nat.find hex - 1) 2 + 1 ≤ 2 * p := by
      rw [Nat.choose_two_right]
      have hsub : Nat.find hex - 1 - 1 = Nat.find hex - 2 := by omega
      rw [hsub]
      omega
    have hB : 2 * p ≤ Nat.choose (Nat.find hex) 2 := by
      rw [Nat.choose_two_right]
      omega
    have hC : 1 < 2 * p := by omega
    have hD : ¬ (2 * p).Prime := Nat.not_prime_mul (by omega) (by omega)
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hA, hB⟩, hC, hD⟩
  have hpd : p ∣ a (Nat.find hex - 1) := by
    have h1 : a (Nat.find hex - 1) = ((Finset.Icc (Nat.choose (Nat.find hex - 1) 2 + 1)
        (Nat.choose (Nat.find hex - 1 + 1) 2)).filter
        (fun k => 1 < k ∧ ¬ k.Prime)).prod id := by
      simp only [a]
    rw [h4] at h1
    rw [h1]
    have hp2p : p ∣ 2 * p := ⟨2, by omega⟩
    exact dvd_trans hp2p (Finset.dvd_prod_of_mem id hrow)
  -- row n contains no multiple of p, so p ∣ a n is impossible
  have hnp : ¬ p ∣ a (Nat.find hex) := by
    intro hpdiv
    have h1 : a (Nat.find hex) = ((Finset.Icc (Nat.choose (Nat.find hex) 2 + 1)
        (Nat.choose (Nat.find hex + 1) 2)).filter
        (fun k => 1 < k ∧ ¬ k.Prime)).prod id := by
      simp only [a]
    rw [h1] at hpdiv
    obtain ⟨k, hk, hkdiv⟩ :=
      (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hprime) id).mp hpdiv
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, hk2⟩, _⟩ := hk
    rw [Nat.choose_two_right] at hk1
    rw [Nat.choose_two_right] at hk2
    have hsub : Nat.find hex + 1 - 1 = Nat.find hex := by omega
    rw [hsub] at hk2
    obtain ⟨j, hj⟩ := hkdiv
    have hkj : k = p * j := hj
    have hj3 : 3 ≤ j := by
      rcases Nat.lt_or_ge j 3 with hcon | hle
      · have hmul : p * j ≤ p * 2 := Nat.mul_le_mul_left p (by omega)
        omega
      · omega
    have hkge : p * 3 ≤ p * j := Nat.mul_le_mul_left p (by omega)
    omega
  exact hnp (dvd_trans hpd hdvd)

end SwarmA93456

theorem swarm_proof :
    ¬ Set.Finite {n : ℕ | 1 < n ∧ ¬ (a (n - 1) ∣ a n)} := by
  intro hfin
  obtain ⟨B, hB⟩ := hfin.exists_le
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes
    (max 23 (B * (B - 1) / 2 / 2 + 1))
  have h23 : 23 ≤ p := le_trans (le_max_left _ _) hp
  have hBp : B * (B - 1) / 2 < 2 * p := by omega
  obtain ⟨n, hn1, hnlow, hfail⟩ := SwarmA93456.key p hprime h23
  have hnB : n ≤ B := hB n ⟨hn1, hfail⟩
  have hmono : n * (n - 1) ≤ B * (B - 1) := Nat.mul_le_mul hnB (by omega)
  omega
