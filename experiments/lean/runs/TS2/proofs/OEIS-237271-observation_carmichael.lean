import FormalConjectures.OEIS.«237271»
import FormalConjecturesForMathlib.NumberTheory.Carmichael

open Nat List Finset

namespace OeisA237271

lemma mem_zip_of_consecutive {l : List ℕ} (h : l.Pairwise (· < ·)) {x y : ℕ} (hx : x ∈ l)
    (hy : y ∈ l) (hxy : x < y) (hnb : ∀ z ∈ l, z ≤ x ∨ y ≤ z) : (x, y) ∈ l.zip l.tail := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.pairwise_cons] at h
    obtain ⟨hall, ht⟩ := h
    rcases List.mem_cons.mp hx with hxa | hxt
    · subst hxa
      rcases List.mem_cons.mp hy with hya | hyt
      · omega
      · cases t with
        | nil => exact absurd hyt List.not_mem_nil
        | cons b s =>
          rcases List.mem_cons.mp hyt with hyb | hys
          · simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
            exact Or.inl (show (x, y) = (x, b) by rw [hyb])
          · rcases Nat.lt_trichotomy y b with h1 | h1 | h1
            · exfalso
              have hbs : b ∈ b :: s := List.mem_cons_self
              have hbmem : b ∈ x :: b :: s := List.mem_cons.mpr (Or.inr hbs)
              have hab : x < b := hall b hbs
              rcases hnb b hbmem with hb | hb
              · omega
              · exfalso
                have hb2 := (List.pairwise_cons.mp ht).1 y hys
                omega
            · simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
              exact Or.inl (show (x, y) = (x, b) by rw [h1])
            · exfalso
              have hbs : b ∈ b :: s := List.mem_cons_self
              have hab : x < b := hall b hbs
              have hbmem : b ∈ x :: b :: s := List.mem_cons.mpr (Or.inr hbs)
              rcases hnb b hbmem with hb | hb
              · omega
              · omega
    · rcases List.mem_cons.mp hy with hya | hyt
      · have hx1 : a < x := hall x hxt
        omega
      · cases t with
        | nil => exact absurd hxt List.not_mem_nil
        | cons b s =>
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
          exact Or.inr (ih ht hxt hyt
            (fun z hz => hnb z (List.mem_cons.mpr (Or.inr hz))))

theorem main : ∀ (k : ℕ), IsCarmichael k → 3 ≤ a k := by
  intro k hk
  obtain ⟨_, hnp, hk1⟩ := hk 1 (by norm_num) (by simp)
  have hcop : k.Coprime (k - 1) := by
    apply Nat.coprime_of_dvd
    intro p hp hp1 hp2
    obtain ⟨d1, e1⟩ := hp1
    obtain ⟨d2, e2⟩ := hp2
    have hd1 : p ∣ 1 := ⟨d1 - d2, by rw [Nat.mul_sub]; omega⟩
    exact absurd (Nat.dvd_one.mp hd1) hp.ne_one
  obtain ⟨hprob, _, _⟩ : FermatPsp k (k - 1) := hk (k - 1) (by omega) hcop
  have hkodd : k % 2 = 1 := by
    rcases Nat.even_or_odd k with heven | hodd
    · exfalso
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      have hpow2 : (m + 1) * (m + 1) = (m + 2) * m + 1 := by ring
      have hmod2 : Nat.ModEq (m + 2) ((m + 1) ^ 2) 1 := by
        show (m + 1) ^ 2 % (m + 2) = 1 % (m + 2)
        rw [pow_two, hpow2, Nat.add_comm ((m + 2) * m) 1, Nat.add_mul_mod_self_left]
      have hem : m % 2 = 0 := by rcases heven with ⟨j, hj⟩; omega
      have hexp : m + 1 = 2 * (m / 2) + 1 := by omega
      have hsplit : (m + 1) ^ (m + 1) = ((m + 1) ^ 2) ^ (m / 2) * (m + 1) := by
        rw [hexp, pow_succ, pow_mul]
      have hf : Nat.ModEq (m + 2) ((m + 1) ^ (m + 1)) (m + 1) := by
        rw [hsplit]
        calc ((m+1)^2)^(m/2) * (m+1) ≡ (1:ℕ)^(m/2) * (m+1) [MOD m+2] :=
              (hmod2.pow (m / 2)).mul (rfl : Nat.ModEq (m + 2) (m + 1) (m + 1))
          _ ≡ m + 1 [MOD m + 2] := by rw [one_pow, one_mul]
      have hf2 : Nat.ModEq (m + 2) ((m + 1) ^ (m + 1)) 1 := by
        obtain ⟨d, hd⟩ := hprob
        have hd' : (m + 1) ^ (m + 1) - 1 = (m + 2) * d := hd
        have hp1' : 1 ≤ (m + 1) ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
        have hh2 : (m + 1) ^ (m + 1) = (m + 2) * d + 1 := by omega
        show (m + 1) ^ (m + 1) % (m + 2) = 1 % (m + 2)
        rw [hh2, Nat.add_comm ((m + 2) * d) 1, Nat.add_mul_mod_self_left]
      have hh : Nat.ModEq (m + 2) (m + 1) 1 := hf.symm.trans hf2
      have hmmod : (m + 1) % (m + 2) = 1 % (m + 2) := hh
      have h2 : (1 : ℕ) % (m + 2) = 1 := Nat.mod_eq_of_lt (by omega)
      have h1 : (m + 1) % (m + 2) = m + 1 := Nat.mod_eq_of_lt (by omega)
      have hmmod2 : (m + 1) % (m + 2) = 1 := by rw [hmmod, h2]
      have hm0 : m = 0 := by omega
      subst hm0
      exact hnp Nat.prime_two
    · obtain ⟨j, hj⟩ := hodd; omega
  -- main computation
  set p1 := k.minFac with hp1def
  have hp1p : p1.Prime := minFac_prime (by omega : k ≠ 1)
  have hp1d : p1 ∣ k := minFac_dvd k
  have hp1ge2 : 2 ≤ p1 := hp1p.two_le
  have hminall : ∀ p, p.Prime → p ∣ k → p1 ≤ p := fun p hp hp' => Nat.minFac_le_of_dvd hp.two_le hp'
  have hkdvd : p1 * (k / p1) = k := Nat.mul_div_cancel' hp1d
  have hq1 : 1 < k / p1 := by
    by_contra hc
    have hpos : 0 < k / p1 := Nat.div_pos (Nat.le_of_dvd (show 0 < k by omega) hp1d) (show 0 < p1 by omega)
    have hone : k / p1 = 1 := by omega
    rw [hone, mul_one] at hkdvd
    exact hnp (by rw [← hkdvd]; exact hp1p)
  have hqle : k / p1 < k := Nat.div_lt_self (by omega) hp1ge2
  set D := k.divisors.sort (· ≤ ·) with hDdef
  have hslt : D.SortedLT := Finset.sortedLT_sort _
  have hmem : ∀ z ∈ D, z ∣ k := by
    intro z hz
    have hz' := (mem_sort (· ≤ ·)).mp hz
    exact (mem_divisors.mp hz').1
  have hd1 : 1 ∈ D := (mem_sort (· ≤ ·)).mpr (mem_divisors.mpr ⟨one_dvd _, by omega⟩)
  have hdp1 : p1 ∈ D := (mem_sort (· ≤ ·)).mpr (mem_divisors.mpr ⟨hp1d, by omega⟩)
  have hdk : k ∈ D := (mem_sort (· ≤ ·)).mpr (mem_divisors.mpr ⟨dvd_refl _, by omega⟩)
  have hdq : k / p1 ∈ D := (mem_sort (· ≤ ·)).mpr (mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hp1d, by omega⟩)
  have hno1 : ∀ z ∈ D, z ≤ 1 ∨ p1 ≤ z := by
    intro z hz
    have hzd : z ∣ k := hmem z hz
    rcases Nat.lt_or_ge z 2 with h | h
    · omega
    · by_contra hc
      have hzp : z.minFac.Prime := minFac_prime (by omega : z ≠ 1)
      have hz1 : z.minFac ∣ k := (Nat.dvd_trans (minFac_dvd z) hzd)
      have := hminall z.minFac hzp hz1
      have := minFac_le (by omega : 0 < z)
      omega
  have hno2 : ∀ z ∈ D, z ≤ k / p1 ∨ k ≤ z := by
    intro z hz
    have hzd : z ∣ k := hmem z hz
    have hzle : z ≤ k := Nat.le_of_dvd (by omega) hzd
    by_contra hc
    have hqz : 2 ≤ k / z := by
      by_contra hqz2
      have hle : k / z ≤ 1 := by omega
      have hkz : z * (k / z) = k := Nat.mul_div_cancel' hzd
      have hmono : z * (k / z) ≤ z := by
        have hmul := Nat.mul_le_mul_left z hle
        rwa [mul_one] at hmul
      omega
    obtain ⟨pp, hpp⟩ : ∃ p, p.Prime ∧ p ∣ k / z :=
      ⟨(k/z).minFac, minFac_prime (by omega), minFac_dvd _⟩
    have hp1q : p1 ≤ k / z := by
      have hpm : (k / z).minFac.Prime := minFac_prime (by omega)
      have hpmd : (k / z).minFac ∣ k / z := minFac_dvd _
      have h1 := hminall _ hpm (Nat.dvd_trans hpmd (Nat.div_dvd_of_dvd hzd))
      exact Nat.le_trans h1 (Nat.minFac_le (show 0 < k / z by omega))
    have hzq : k / (k / z) = z := by
      have hkz2 : z * (k / z) = k := Nat.mul_div_cancel' hzd
      refine Nat.div_eq_of_eq_mul_left (show 0 < k / z by omega) ?_
      exact hkz2.symm
    have hle : k / (k / z) ≤ k / p1 := Nat.div_le_div_left hp1q (show 0 < p1 by omega)
    rw [hzq] at hle
    omega
  have hP1 : (1, p1) ∈ D.zip D.tail :=
    mem_zip_of_consecutive (List.sortedLT_iff_pairwise.mp hslt) hd1 hdp1 (by omega) hno1
  have hP2 : (k / p1, k) ∈ D.zip D.tail :=
    mem_zip_of_consecutive (List.sortedLT_iff_pairwise.mp hslt) hdq hdk hqle hno2
  have hoddP : p1 % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp1p with h | h
    · exfalso
      have h2k : 2 ∣ k := by rw [← h]; exact hp1d
      obtain ⟨q, hq⟩ := h2k
      omega
    · exact h
  have hkmul : 2 * (k / p1) ≤ k := by
    have h := Nat.mul_le_mul_right (k / p1) hp1ge2
    rwa [hkdvd] at h
  -- final count
  have hL1 : (1, p1) ∈ (D.zip D.tail).filter (fun pair => Odd pair.2 ∧ pair.2 ≥ 2 * pair.1) :=
    List.mem_filter.mpr ⟨hP1, by
      simp only [decide_eq_true_eq]
      exact ⟨⟨p1 / 2, by omega⟩, by omega⟩⟩
  have hL2 : (k / p1, k) ∈ (D.zip D.tail).filter (fun pair => Odd pair.2 ∧ pair.2 ≥ 2 * pair.1) :=
    List.mem_filter.mpr ⟨hP2, by
      simp only [decide_eq_true_eq]
      exact ⟨⟨k / 2, by omega⟩, by omega⟩⟩
  have hne : (1, p1) ≠ (k / p1, k) := by
    intro hc; rw [Prod.mk.injEq] at hc; obtain ⟨hc1, _⟩ := hc; omega
  have hcount : 2 ≤ (D.zip D.tail).countP
      (fun pair => decide (Odd pair.2 ∧ pair.2 ≥ 2 * pair.1)) := by
    rw [countP_eq_length_filter]
    have he1 : (k / p1, k) ∈ ((D.zip D.tail).filter
        (fun pair => decide (Odd pair.2 ∧ pair.2 ≥ 2 * pair.1))).erase (1, p1) :=
      (List.mem_erase_of_ne (Ne.symm hne)).mpr hL2
    have hpos : 0 < (((D.zip D.tail).filter
        (fun pair => decide (Odd pair.2 ∧ pair.2 ≥ 2 * pair.1))).erase (1, p1)).length :=
      List.length_pos_of_mem he1
    have hlen := List.length_erase_of_mem hL1
    omega
  have ha2 : a k = 1 + (D.zip D.tail).countP
      (fun pair => decide (Odd pair.2 ∧ pair.2 ≥ 2 * pair.1)) := rfl
  rw [ha2]
  omega

end OeisA237271

theorem swarm_proof (k : ℕ) (hk : IsCarmichael k) : 3 ≤ OeisA237271.a k :=
  OeisA237271.main k hk
