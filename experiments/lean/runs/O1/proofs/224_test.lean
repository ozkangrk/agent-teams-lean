import FormalConjectures.OEIS.«224»

/-!
# Ordowski conjecture (A000224) : a(n)·(a(n)-1) | n²-1 iff n odd prime (n>1).
-/

open OeisA224

namespace OeisA224Proof

/-- `0` and `1` are distinct squares mod `n` for `2 ≤ n`, so `a n ≥ 2`. -/
lemma two_le_a {n : ℕ} (hn : 2 ≤ n) : 2 ≤ a n := by
  unfold a
  by_cases h0 : n = 0
  · omega
  · rw [if_neg h0]
    have e0 : (0:ℕ) ∈ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) :=
      Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), by simp⟩
    have e1 : (1:ℕ) ∈ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
      refine Finset.mem_image.2 ⟨1, Finset.mem_range.2 (by omega), ?_⟩
      have h : (1:ℕ) ^ 2 % n = 1 % n := by simp
      rw [h, Nat.mod_eq_of_lt hn]
    have hsub : ({0, 1} : Finset ℕ) ⊆ (Finset.range n).image (fun k : ℕ => k ^ 2 % n) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact e0
      · exact e1
    have hcard := Finset.card_le_card hsub
    simpa using hcard

/-- Even `n ≥ 2` fails the congruence (parity). -/
lemma even_fail {n : ℕ} (hn : 2 ≤ n) (heven : Even n) :
    ¬ (n ^ 2 ≡ 1 [MOD a n * (a n - 1)]) := by
  have h2 : 2 ≤ a n := two_le_a hn
  have hmeven : 2 ∣ a n * (a n - 1) := by
    rcases Nat.even_or_odd (a n) with h | h
    · obtain ⟨r, hr⟩ := h
      have : a n = 2 * r := by omega
      rw [this]
      have hrw : 2 * r * (2 * r - 1) = 2 * (r * (2 * r - 1)) := by ring
      rw [hrw]
      exact (dvd_refl (2:ℕ)).mul_right (r * (2 * r - 1))
    · obtain ⟨k, hk⟩ := h
      have he : a n - 1 = 2 * k := by omega
      have hrw : a n * (2 * k) = 2 * (a n * k) := by ring
      rw [he, hrw]
      exact (dvd_refl (2:ℕ)).mul_right (a n * k)
  intro hcong
  have h1m : 1 < a n * (a n - 1) := by
    calc 1 < a n := by omega
      _ ≤ a n * (a n - 1) := Nat.le_mul_of_pos_right (a n) (by omega)
  have h1 : n ^ 2 % (a n * (a n - 1)) = 1 := by
    have hc := hcong
    rw [Nat.ModEq, Nat.mod_eq_of_lt h1m] at hc
    exact hc
  have h2' : (n ^ 2 % (a n * (a n - 1))) % 2 = n ^ 2 % 2 := Nat.mod_mod_of_dvd _ hmeven
  rw [h1] at h2'
  rcases heven with ⟨k, hk⟩
  have hn2 : n ^ 2 % 2 = 0 := by
    rw [hk]
    have h4 : (k + k) ^ 2 = 2 * (2 * k * k) := by ring
    rw [h4, Nat.mul_mod_right]
  have hone : (1:ℕ) % 2 = 1   := by decide
  omega



/-! ### Squares mod an odd prime -/

/-- Helper: a factorization identity `x*x = y*y + p*(x-y)` gives `x² ≡ y² [MOD p]`. -/
lemma sq_mod_of_fac {p x y : ℕ} (h : x * x = y * y + p * (x - y)) : x ^ 2 % p = y ^ 2 % p := by
  rw [Nat.pow_two, Nat.pow_two, h, Nat.add_mul_mod_self_left]

/-- If `k + l = p` then `k² ≡ l² [MOD p]`. -/
lemma sq_mod_eq_of_sum {p k l : ℕ} (h : k + l = p) : k ^ 2 % p = l ^ 2 % p := by
  rcases Nat.le_total l k with hle | hle
  · refine sq_mod_of_fac (x := k) (y := l) ?_
    have hz : ((k : ℤ) * k - (l : ℤ) * l) = (((k - l : ℕ) : ℤ)) * ((p : ℤ)) := by
      have hzs : ((k : ℤ) * k - (l : ℤ) * l) = ((k : ℤ) - (l : ℤ)) * ((k : ℤ) + (l : ℤ)) := by ring
      have hkp : ((k : ℤ) + (l : ℤ)) = ((p : ℤ)) := by push_cast; omega
      have hsub : ((k : ℤ) - (l : ℤ)) = ((k - l : ℕ) : ℤ) := (Int.natCast_sub hle).symm
      rw [hsub, hkp] at hzs
      exact hzs
    have hf : ((k * k : ℕ) : ℤ) = ((l * l : ℕ) : ℤ) + ((p * (k - l) : ℕ) : ℤ) := by
      push_cast; linarith [hz]
    exact_mod_cast hf
  · refine (sq_mod_of_fac (x := l) (y := k) ?_).symm
    have hz : ((l : ℤ) * l - (k : ℤ) * k) = (((l - k : ℕ) : ℤ)) * ((p : ℤ)) := by
      have hzs : ((l : ℤ) * l - (k : ℤ) * k) = ((l : ℤ) - (k : ℤ)) * ((l : ℤ) + (k : ℤ)) := by ring
      have hkp : ((l : ℤ) + (k : ℤ)) = ((p : ℤ)) := by push_cast; omega
      have hsub : ((l : ℤ) - (k : ℤ)) = ((l - k : ℕ) : ℤ) := (Int.natCast_sub hle).symm
      rw [hsub, hkp] at hzs
      exact hzs
    have hf : ((l * l : ℕ) : ℤ) = ((k * k : ℕ) : ℤ) + ((p * (l - k) : ℕ) : ℤ) := by
      push_cast; linarith [hz]
    exact_mod_cast hf

/-- For an odd prime `p`, the squares `k² % p` with `k < (p+1)/2` are pairwise distinct. -/
lemma sq_inj_half {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k l : ℕ}
    (hk : k < (p + 1) / 2) (hl : l < (p + 1) / 2) (hmod : k ^ 2 % p = l ^ 2 % p) : k = l := by
  obtain ⟨r, hr⟩ := hp.odd_of_ne_two hp2
  have h2m : 2 * ((p + 1) / 2) = p + 1 := by omega
  have hkl : k + l < p := by omega
  rw [Nat.pow_two, Nat.pow_two] at hmod
  have hdvd0 : (p:ℤ) ∣ (l * l : ℕ) - (k * k : ℕ) := (Nat.modEq_iff_dvd).1 hmod
  have hpush0 : ((l * l : ℕ) - (k * k : ℕ)) = ((l : ℤ) * l - (k : ℤ) * k) := by
    push_cast; ring
  rw [hpush0] at hdvd0
  rcases Nat.le_total l k with hle | hle
  · -- l ≤ k
    have hdvd : (p:ℤ) ∣ ((k : ℤ) * k - (l : ℤ) * l) := by
      rcases hdvd0 with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      push_cast at hc ⊢
      linarith
    have hkey : ((k : ℤ) * k - (l : ℤ) * l) = (((k - l) * (k + l) : ℕ) : ℤ) := by
      have hzs : ((k : ℤ) * k - (l : ℤ) * l) = ((k : ℤ) - (l : ℤ)) * ((k : ℤ) + (l : ℤ)) := by ring
      have hsub : ((k : ℤ) - (l : ℤ)) = ((k - l : ℕ) : ℤ) := (Int.natCast_sub hle).symm
      rw [hsub] at hzs
      push_cast at hzs
      exact hzs
    rw [hkey] at hdvd
    have hnat : p ∣ (k - l) * (k + l) := Int.natCast_dvd_natCast.1 hdvd
    rcases hp.dvd_mul.1 hnat with h1 | h2
    · -- p ∣ k - l
      rcases Nat.eq_zero_or_pos (k - l) with h0 | h0
      · omega
      · have hdl : k - l < p := by omega
        exact absurd (Nat.le_of_dvd h0 h1) (Nat.not_le.2 hdl)
    · -- p ∣ k + l
      rcases Nat.eq_zero_or_pos (k + l) with h0 | h0
      · omega
      · exact absurd (Nat.le_of_dvd h0 h2) (Nat.not_le.2 hkl)
  · -- k ≤ l
    have hkey : ((l : ℤ) * l - (k : ℤ) * k) = (((l - k) * (l + k) : ℕ) : ℤ) := by
      have hzs : ((l : ℤ) * l - (k : ℤ) * k) = ((l : ℤ) - (k : ℤ)) * ((l : ℤ) + (k : ℤ)) := by ring
      have hsub : ((l : ℤ) - (k : ℤ)) = ((l - k : ℕ) : ℤ) := (Int.natCast_sub hle).symm
      rw [hsub] at hzs
      push_cast at hzs
      exact hzs
    rw [hkey] at hdvd0
    have hnat : p ∣ (l - k) * (l + k) := Int.natCast_dvd_natCast.1 hdvd0
    rcases hp.dvd_mul.1 hnat with h1 | h2
    · -- p ∣ l - k
      rcases Nat.eq_zero_or_pos (l - k) with h0 | h0
      · omega
      · have hdl : l - k < p := by omega
        exact absurd (Nat.le_of_dvd h0 h1) (Nat.not_le.2 hdl)
    · -- p ∣ l + k
      rcases Nat.eq_zero_or_pos (l + k) with h0 | h0
      · omega
      · have hkl2 : l + k < p := by omega
        exact absurd (Nat.le_of_dvd h0 h2) (Nat.not_le.2 hkl2)

/-- For an odd prime `p`, there are exactly `(p+1)/2` squares mod `p`. -/
lemma a_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : a p = (p + 1) / 2 := by
  have hppos : 0 < p := hp.pos
  obtain ⟨r, hr⟩ := hp.odd_of_ne_two hp2
  have h2m : 2 * ((p + 1) / 2) = p + 1 := by omega
  have himg : (Finset.range p).image (fun k : ℕ => k ^ 2 % p)
            = (Finset.range ((p + 1) / 2)).image (fun k : ℕ => k ^ 2 % p) := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_image.1 hx with ⟨k, hk, rfl⟩
      have hklt : k < p := Finset.mem_range.1 hk
      rcases Nat.lt_or_ge k ((p + 1) / 2) with hkm | hkm
      · exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hkm, rfl⟩
      · have hkl : p - k < (p + 1) / 2 := by omega
        have hsum : k + (p - k) = p := by omega
        have hs := sq_mod_eq_of_sum hsum
        exact Finset.mem_image.2 ⟨p - k, Finset.mem_range.2 hkl, hs.symm⟩
    · intro x hx
      rcases Finset.mem_image.1 hx with ⟨k, hk, rfl⟩
      have hklt : k < (p + 1) / 2 := Finset.mem_range.1 hk
      have hk' : k < p := by omega
      exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 hk', rfl⟩
  have hinj : Set.InjOn (fun k : ℕ => k ^ 2 % p) ↑(Finset.range ((p + 1) / 2)) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_range] at hx hy
    exact sq_inj_half hp hp2 hx hy hxy
  have hne : p ≠ 0 := by omega
  unfold a
  rw [if_neg hne, himg, Finset.card_image_of_injOn hinj]
  simp



/-- Odd primes satisfy the congruence. -/
lemma odd_prime_ok (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ 2 ≡ 1 [MOD a p * (a p - 1)] := by
  have hap : a p = (p + 1) / 2 := a_prime p hp hp2
  obtain ⟨r, hr⟩ := hp.odd_of_ne_two hp2
  have hple : 2 ≤ p := hp.two_le
  have hr1 : 1 ≤ r := by omega
  have hrm : (p + 1) / 2 = r + 1 := by
    have hp1 : p + 1 = 2 * (r + 1) := by omega
    rw [hp1, Nat.mul_div_cancel_left _ (by norm_num)]
  have hprod : a p * (a p - 1) = (r + 1) * r := by
    rw [hap, hrm, Nat.add_sub_cancel]
  have hX : p ^ 2 = 1 + 4 * ((r + 1) * r) := by rw [hr]; ring
  rw [hprod]
  show p ^ 2 % ((r + 1) * r) = 1 % ((r + 1) * r)
  rw [hX, Nat.add_mul_mod_self_right]


/-! Semantic checks (verified earlier): `a 5 = 3`, `a 9 = 4`, `a 21 = 8` hold by `decide`. -/

end OeisA224Proof
