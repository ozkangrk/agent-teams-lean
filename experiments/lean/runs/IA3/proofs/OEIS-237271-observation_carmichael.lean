import FormalConjectures.OEIS.«237271»
import FormalConjectures.Wikipedia.AgohGiuga

/-! Swarm proof for OEIS A237271 observation_carmichael: 3 <= a k for a
Carmichael number k.  Carmichael numbers are odd and composite.  For any
odd composite k with smallest prime factor p, the sorted divisor list of k
contains the adjacent pairs (1, p) and (k/p, k), and both satisfy the
countP predicate `Odd second /\ second >= 2 * first`.  Hence
a k = 1 + countP >= 3. -/

namespace S237271C

open List Finset Nat

theorem countP_ge_one {α : Type} (p : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l → p x → 1 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
    intro x hx hpx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [List.countP_cons, if_pos hpx]; omega
    · have h := ih x hx hpx
      rw [List.countP_cons]
      by_cases hpa : p a = true
      · rw [if_pos hpa]; omega
      · rw [if_neg hpa]; omega

theorem countP_ge_two {α : Type} (p : α → Bool) :
    ∀ (l : List α) (x y : α), x ≠ y → x ∈ l → y ∈ l → p x → p y →
    2 ≤ l.countP p := by
  intro l
  induction l with
  | nil => intro x y _ hx; simp at hx
  | cons a t ih =>
    intro x y hxy hx hy hpx hpy
    rcases List.mem_cons.mp hx with rfl | hx
    · have hyt : y ∈ t := by
        rcases List.mem_cons.mp hy with hya | hyt
        · exact absurd hya (Ne.symm hxy)
        · exact hyt
      have h1 := countP_ge_one p t y hyt hpy
      rw [List.countP_cons, if_pos hpx]
      omega
    · rcases List.mem_cons.mp hy with rfl | hy
      · have hxt : x ∈ t := by
          rcases List.mem_cons.mp hx with hxa | hxt
          · exact absurd hxa hxy
          · exact hxt
        have h1 := countP_ge_one p t x hxt hpx
        rw [List.countP_cons, if_pos hpy]
        omega
      · have h2 := ih x y hxy hx hy hpx hpy
        rw [List.countP_cons]
        by_cases hpa : p a = true
        · rw [if_pos hpa]; omega
        · rw [if_neg hpa]; omega

theorem adj_mem_zip : ∀ (l : List ℕ), l.Pairwise (· ≤ ·) → l.Nodup →
    ∀ (x y : ℕ), x ∈ l → y ∈ l → x < y → (∀ z ∈ l, z ≤ x ∨ y ≤ z) →
    (x, y) ∈ l.zip l.tail := by
  intro l
  induction l with
  | nil => intro _ _ x y hx; simp at hx
  | cons a t ih =>
    intro hl hnd x y hx hy hlt hnb
    obtain ⟨hale, hltt⟩ := List.pairwise_cons.mp hl
    rcases List.mem_cons.mp hx with rfl | hxt
    · have hyt : y ∈ t := by
        rcases List.mem_cons.mp hy with hya | hyt
        · omega
        · exact hyt
      rcases t with _ | ⟨b, t'⟩
      · simp at hyt
      · have hba : x ≤ b := hale b (by simp)
        have hby : b = y := by
          by_contra hne
          have hyt' : y ∈ t' := by
            rcases List.mem_cons.mp hyt with hyb | hyt'
            · exact absurd hyb (Ne.symm hne)
            · exact hyt'
          have hble : b ≤ y := (List.pairwise_cons.mp hltt).1 y hyt'
          have hyle : y ≤ b :=
            ((hnb b (by simp)) : b ≤ x ∨ y ≤ b).resolve_left (fun hb => by
              have hbe : b = x := Nat.le_antisymm hb hba
              exact (List.nodup_cons.mp hnd).1 (by rw [← hbe]; simp))
          omega
        rw [hby]
        exact List.mem_cons_self
    · have hyt : y ∈ t := by
        rcases List.mem_cons.mp hy with hya | hyt
        · have hax : a ≤ x := hale x hxt; omega
        · exact hyt
      have ihres := ih hltt ((List.nodup_cons.mp hnd).2) x y hxt hyt hlt
        (fun z hz => hnb z (by simp [hz]))
      rcases t with _ | ⟨b, t'⟩
      · simp at hxt
      · exact List.mem_cons_of_mem _ ihres

theorem main_le (k : ℕ) (hk1 : 1 < k) (hknp : ¬ k.Prime) (hkodd : Odd k) :
    3 ≤ OeisA237271.a k := by
  have h0 : k ≠ 0 := by omega
  set p := k.minFac with hpdef
  have hp : p.Prime := k.minFac_prime (by omega)
  have hp2 : 2 ≤ p := hp.two_le
  have hpd : p ∣ k := k.minFac_dvd
  have hpe2 : p ≠ 2 := by
    intro h2e
    rw [h2e] at hpd
    obtain ⟨m, hm⟩ := hkodd
    obtain ⟨c, hc⟩ := hpd
    omega
  have hp3 : 3 ≤ p := by omega
  have hpmod : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hpe2
  have hkeq : p * (k / p) = k := Nat.mul_div_cancel' hpd
  have hq1 : 1 ≤ k / p := by
    by_contra h
    push_neg at h
    have hz : k / p = 0 := Nat.lt_one_iff.mp h
    have hc := hkeq
    rw [hz, Nat.mul_zero] at hc
    omega
  have hge2 : 2 * (k / p) ≤ p * (k / p) := Nat.mul_le_mul hp2 (le_refl _)
  have h3 : 2 * (k / p) ≤ k := Nat.le_trans hge2 (by rw [hkeq])
  have hqltk : k / p < k := by omega
  have hmem : ∀ d, d ∈ OeisA237271.sortedDivisorsList k ↔ d ∣ k := by
    intro d
    rw [OeisA237271.sortedDivisorsList, (Finset.mem_sort (· ≤ ·)), Nat.mem_divisors]
    simp [h0]
  have h1m : 1 ∈ OeisA237271.sortedDivisorsList k := (hmem 1).mpr (one_dvd k)
  have hpm : p ∈ OeisA237271.sortedDivisorsList k := (hmem p).mpr hpd
  have hnb1 : ∀ z ∈ OeisA237271.sortedDivisorsList k, z ≤ 1 ∨ p ≤ z := by
    intro z hz
    obtain ⟨w, hw⟩ := (hmem z).mp hz
    have hz1 : 1 ≤ z := by
      rcases Nat.lt_or_ge z 1 with hz' | hz'
      · rw [show z = 0 from by omega, Nat.zero_mul] at hw; omega
      · exact hz'
    rcases Nat.lt_or_ge z 2 with hz2 | hz2
    · left; omega
    · right; exact Nat.minFac_le_of_dvd hz2 ⟨w, hw⟩
  have hpred1 := adj_mem_zip (OeisA237271.sortedDivisorsList k)
      (Finset.pairwise_sort _ (· ≤ ·)) (Finset.sort_nodup _ (· ≤ ·))
      1 p h1m hpm (by omega) hnb1
  have hqpm : (k / p) ∈ OeisA237271.sortedDivisorsList k :=
    (hmem _).mpr ⟨p, by rw [Nat.mul_comm]; exact hkeq.symm⟩
  have hkm : k ∈ OeisA237271.sortedDivisorsList k := (hmem k).mpr (dvd_refl k)
  have hnb2 : ∀ z ∈ OeisA237271.sortedDivisorsList k, z ≤ k / p ∨ k ≤ z := by
    intro z hz
    obtain ⟨w, hw⟩ := (hmem z).mp hz
    rcases Nat.lt_or_ge w 2 with hw2 | hw2
    · rcases Nat.lt_or_ge w 1 with hw1 | hw1
      · rw [show w = 0 from by omega, Nat.mul_zero] at hw; omega
      · have hwE : w = 1 := Nat.le_antisymm (by omega) hw1
        rw [hwE, Nat.mul_one] at hw; omega
    · have hwk : w ∣ k := ⟨z, by rw [Nat.mul_comm]; exact hw⟩
      have hplew : p ≤ w := Nat.minFac_le_of_dvd hw2 hwk
      by_contra hcon
      push_neg at hcon
      have h1' : (k / p + 1) * p ≤ z * w := Nat.mul_le_mul (by omega) hplew
      have hkp : (k / p) * p = k := by rw [Nat.mul_comm]; exact hkeq
      have h2' : (k / p + 1) * p = k + p := by
        rw [Nat.add_mul, hkp, Nat.one_mul]
      rw [← hw] at h1'
      rw [h2'] at h1'
      omega
  have hpred2 := adj_mem_zip (OeisA237271.sortedDivisorsList k)
      (Finset.pairwise_sort _ (· ≤ ·)) (Finset.sort_nodup _ (· ≤ ·))
      (k / p) k hqpm hkm hqltk hnb2
  have hne : (1, p) ≠ (k / p, k) := by
    intro heq
    have hfst : 1 = k / p := congrArg Prod.fst heq
    have hc := hkeq
    rw [← hfst, Nat.mul_one] at hc
    exact hknp (hc ▸ hp)
  have hwit1 : (fun pr : ℕ × ℕ => decide (Odd pr.2 ∧ pr.2 ≥ 2 * pr.1)) (1, p) = true := by
    rw [decide_eq_true_eq]
    exact ⟨Nat.odd_iff.mpr hpmod, by omega⟩
  have hwit2 : (fun pr : ℕ × ℕ => decide (Odd pr.2 ∧ pr.2 ≥ 2 * pr.1)) (k / p, k) = true := by
    rw [decide_eq_true_eq]
    refine ⟨hkodd, ?_⟩
    exact h3
  have hcnt : 2 ≤ ((OeisA237271.sortedDivisorsList k).zip
      ((OeisA237271.sortedDivisorsList k).tail)).countP
      (fun pr : ℕ × ℕ => decide (Odd pr.2 ∧ pr.2 ≥ 2 * pr.1)) :=
    countP_ge_two _ _ _ _ hne hpred1 hpred2 hwit1 hwit2
  rw [show OeisA237271.a k = 1 + ((OeisA237271.sortedDivisorsList k).zip
      ((OeisA237271.sortedDivisorsList k).tail)).countP
      (fun pr : ℕ × ℕ => decide (Odd pr.2 ∧ pr.2 ≥ 2 * pr.1)) from rfl]
  omega

end S237271C

theorem swarm_proof (k : ℕ) (hk : IsCarmichael k) :
    3 ≤ OeisA237271.a k := by
  have hpsp := hk 1 (by omega) (Nat.coprime_one_right k)
  have hnp : ¬ k.Prime := hpsp.2.1
  have h1 : 1 < k := hpsp.2.2
  have hcomp : k.Composite := ⟨h1, hnp⟩
  obtain ⟨hsf, hkors⟩ := (AgohGiuga.korselts_criterion k hcomp).mp hk
  have hodd : Odd k := by
    by_contra hnotodd
    have hE : 2 ∣ k := by
      rcases Nat.even_or_odd k with he | ho
      · exact Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp he)
      · exact absurd ho hnotodd
    obtain ⟨t, ht⟩ := hE
    have hk2 : k ≠ 2 := fun h => hnp (h ▸ Nat.prime_two)
    have ht1 : 2 ≤ t := by omega
    have hq : t.minFac.Prime := t.minFac_prime (by omega)
    have hqd : t.minFac ∣ t := t.minFac_dvd
    have hqdk : t.minFac ∣ k := by
      obtain ⟨s, hs⟩ := hqd
      refine ⟨2 * s, ?_⟩
      calc k = 2 * t := ht
      _ = 2 * (t.minFac * s) := by rw [← hs]
      _ = t.minFac * (2 * s) := by ring
    have hq2 : t.minFac ≠ 2 := by
      intro hqe
      rw [hqe] at hqd
      obtain ⟨s, hs⟩ := hqd
      have h4 : 2 * 2 ∣ k := by
        refine ⟨s, ?_⟩
        calc k = 2 * t := ht
        _ = 2 * (2 * s) := by rw [← hs]
        _ = 2 * 2 * s := by ring
      exact ((Nat.squarefree_iff_prime_squarefree).mp hsf 2 Nat.prime_two) h4
    have hqo : t.minFac % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
    have hkor : t.minFac - 1 ∣ k - 1 := hkors t.minFac hq hqdk
    have h2q1 : 2 ∣ t.minFac - 1 := by
      refine ⟨(t.minFac - 1) / 2, ?_⟩
      omega
    have h2k1 : 2 ∣ k - 1 := Nat.dvd_trans h2q1 hkor
    obtain ⟨c, hc⟩ := h2k1
    omega
  exact S237271C.main_le k h1 hnp hodd
