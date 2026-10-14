import FormalConjectures.OEIS.«237271»

/-! Submission for OEIS-237271-observation_carmichael -/

open Nat Finset List

theorem mem_zip_of_sorted {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) (hnd : L.Nodup) {x y : ℕ}
    (hx : x ∈ L) (hy : y ∈ L) (hxy : x < y) (hgap : ∀ z ∈ L, x < z → y ≤ z) :
    (x, y) ∈ L.zip L.tail := by
  induction L with
  | nil => simp at hx
  | cons u t ih =>
    obtain ⟨hu, hst⟩ := List.pairwise_cons.1 hs
    obtain ⟨hunut, hndt⟩ := List.nodup_cons.1 hnd
    have hgapt : ∀ z ∈ t, x < z → y ≤ z := fun z hz => hgap z (by simp [hz])
    rcases List.mem_cons.1 hx with rfl | hxt
    · have hyt : y ∈ t := by
        rcases List.mem_cons.1 hy with rfl | h
        · omega
        · exact h
      obtain ⟨w, t2, rfl⟩ : ∃ w t2, t = w :: t2 := by
        cases t with
        | nil => simp at hyt
        | cons a l => exact ⟨a, l, rfl⟩
      have hxw : x ≤ w := hu w (by simp)
      have hyw : y = w := by
        rcases List.mem_cons.1 hyt with rfl | hyy
        · rfl
        · obtain ⟨hw1, _⟩ := List.pairwise_cons.1 hst
          have hltw : x < w := by
            have hne : x ≠ w := fun h => hunut (by rw [h]; exact List.mem_cons_self)
            omega
          have h3 : y ≤ w := hgap w (by simp) hltw
          have h4 : w ≤ y := hw1 y (by simp [hyy])
          omega
      show (x, y) ∈ (x :: w :: t2).zip (w :: t2)
      have hgoal : (x :: w :: t2).zip (w :: t2) = (x, w) :: (w :: t2).zip t2 := rfl
      rw [hgoal, hyw]
      exact List.mem_cons_self
    · have hux : u ≤ x := hu x hxt
      have hyt : y ∈ t := by
        rcases List.mem_cons.1 hy with rfl | h
        · omega
        · exact h
      have hmem := ih hst hndt hxt hyt hgapt
      cases t with
      | nil => simp at hxt
      | cons w t2 =>
        cases t2 with
        | nil => simp at hmem
        | cons v t3 =>
          show (x, y) ∈ (u :: w :: v :: t3).zip (w :: v :: t3)
          have hgoal : (u :: w :: v :: t3).zip (w :: v :: t3)
              = (u, w) :: (w :: v :: t3).zip (v :: t3) := rfl
          rw [hgoal]
          exact List.mem_cons_of_mem _ hmem


theorem swarm_proof (k : ℕ) (hk : IsCarmichael k) : 3 ≤ OeisA237271.a k := by
  have h1 : 1 < k ∧ ¬ k.Prime := by
    have h := hk 1 (by norm_num) (by norm_num)
    exact ⟨h.2.2, h.2.1⟩
  have hk2 : 2 ≤ k := h1.1
  have kodd : Odd k := by
    by_contra hev
    have hmod2 : k % 2 = 0 := Nat.not_odd_iff.1 hev
    have hk4 : 4 ≤ k := by
      have : k ≠ 2 := fun h => h1.2 (h ▸ Nat.prime_two)
      have : k ≠ 3 := by omega
      omega
    have hcop : k.Coprime (k - 1) := by
      rw [Nat.coprime_self_sub_right (by omega)]
      exact Nat.coprime_one_right k
    have hfp := hk (k - 1) (by omega) hcop
    have hdvd : k ∣ (k - 1) ^ (k - 1) - 1 := hfp.1
    have hmodZ : ((k : ℤ) - 1) ≡ -1 [ZMOD (k : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have : (-1 : ℤ) - ((k : ℤ) - 1) = -((k : ℤ)) := by ring
      rw [this]
      exact dvd_neg.mpr (dvd_refl _)
    have hodd2 : Odd (k - 1) := Nat.odd_iff.2 (by omega)
    have hpowZ : (((k : ℤ) - 1) ^ (k - 1)) ≡ (-1 : ℤ) [ZMOD (k : ℤ)] := by
      have h := hmodZ.pow (k - 1)
      rw [hodd2.neg_one_pow] at h
      exact h
    have hdvdZ : ((k : ℤ)) ∣ (((k : ℤ) - 1) ^ (k - 1) - 1) := by
      have hc0 : ((k : ℤ)) ∣ ((((k - 1 : ℕ)) ^ (k - 1) - 1 : ℕ) : ℤ) := by
        rw [Int.natCast_dvd_natCast]
        exact hdvd
      have hpos : 0 < ((k - 1 : ℕ)) ^ (k - 1) := Nat.pow_pos (by omega)
      have e1 : (((((k - 1 : ℕ)) ^ (k - 1) - 1 : ℕ) : ℤ))
          = (((((k - 1 : ℕ)) : ℤ)) ^ (k - 1) - 1) := by
        rw [Nat.cast_sub (by omega), Int.natCast_pow, Int.natCast_one]
      have e2 : (((((k - 1 : ℕ)) : ℤ)) ^ (k - 1)) = ((k : ℤ) - 1) ^ (k - 1) := by
        rw [Int.natCast_sub (by omega), Int.natCast_one]
      rw [e1, e2] at hc0
      exact hc0
    have hfin : ((k : ℤ)) ∣ (2 : ℤ) := by
      have hA := hdvdZ
      have hB := (Int.modEq_iff_dvd).1 hpowZ
      have hsum := hA.add hB
      have hnum : ((((k : ℤ) - 1) ^ (k - 1) - 1) + (-1 - ((k : ℤ) - 1) ^ (k - 1))) = -2 := by ring
      rw [hnum] at hsum
      exact dvd_neg.mpr hsum
    have hkdv2 : k ∣ 2 := Int.natCast_dvd_natCast.mp hfin
    have hkle : k ≤ 2 := Nat.le_of_dvd (by norm_num) hkdv2
    omega
  obtain ⟨p, hpdef⟩ : ∃ p, k.minFac = p := ⟨_, rfl⟩
  have hpprime : p.Prime := by
    rw [← hpdef]
    exact Nat.minFac_prime (by omega)
  have hp1 : 1 < p := hpprime.one_lt
  have hpd : p ∣ k := hpdef ▸ Nat.minFac_dvd k
  have podd : Odd p := by
    rcases Nat.Prime.eq_two_or_odd hpprime with h | h
    · exfalso
      rw [h] at hpd
      rcases hpd with ⟨t, ht⟩
      have hkmod : k % 2 = 0 := by omega
      have := Nat.odd_iff.1 kodd
      omega
    · exact Nat.odd_iff.2 h
  have p3 : 3 ≤ p := by
    have := Nat.odd_iff.1 podd
    omega
  obtain ⟨q, hqdef⟩ : ∃ q, k / p = q := ⟨_, rfl⟩
  have hkpq : k = p * q := by
    rw [← hqdef]
    exact (Nat.mul_div_cancel' hpd).symm
  have qdvd : q ∣ k := by
    rw [hkpq, Nat.mul_comm]
    exact dvd_mul_right _ _
  have qge3 : 3 ≤ q := by
    by_contra hc
    have hq2 : q ≤ 2 := by omega
    rcases Nat.lt_or_ge q 2 with hq0 | hq0
    · rcases Nat.lt_or_ge q 1 with hqA | hqA
      · have hq0e : q = 0 := by omega
        rw [hq0e, Nat.mul_zero] at hkpq
        omega
      · have hq1e : q = 1 := by omega
        rw [hq1e, Nat.mul_one] at hkpq
        exact h1.2 (hkpq ▸ hpprime)
    · have hq2e : q = 2 := by omega
      have h2dvd : 2 ∣ k := by
        rw [hkpq, hq2e, Nat.mul_comm]
        exact dvd_mul_right 2 p
      rcases h2dvd with ⟨t, ht⟩
      have := Nat.odd_iff.1 kodd
      omega
  have qltk : q < k := by
    have hstep1 : q * 3 ≤ q * p := Nat.mul_le_mul_left q p3
    have hstep2 : q * 3 ≤ p * q := by rw [Nat.mul_comm p q]; exact hstep1
    have hlt : q < q * 3 := by omega
    have hfin : q < p * q := Nat.lt_of_lt_of_le hlt hstep2
    omega
  have qle : ∀ d, d ∣ k → d < k → d ≤ q := by
    intro d hdvd2 hdlt
    obtain ⟨r, hrdef⟩ : ∃ r, k / d = r := ⟨_, rfl⟩
    have hkd : k = d * r := by
      rw [← hrdef]
      exact (Nat.mul_div_cancel' hdvd2).symm
    have hr2 : 2 ≤ r := by
      rcases Nat.lt_or_ge r 2 with hlt2 | hge2
      · rcases Nat.lt_or_ge r 1 with h0 | h0
        · have h0e : r = 0 := by omega
          rw [h0e, Nat.mul_zero] at hkd
          omega
        · have h1e : r = 1 := by omega
          rw [h1e, Nat.mul_one] at hkd
          omega
      · exact hge2
    have hrd : r ∣ k := by
      rw [hkd, Nat.mul_comm]
      exact dvd_mul_right r d
    have hple : p ≤ r := hpdef ▸ Nat.minFac_le_of_dvd hr2 hrd
    have hke : d * r = p * q := by omega
    have hdq : d * p ≤ d * r := Nat.mul_le_mul_left d hple
    rw [hke] at hdq
    rw [Nat.mul_comm d p] at hdq
    exact Nat.le_of_mul_le_mul_left hdq (by omega)
  set L := k.divisors.sort (· ≤ ·) with hLdef
  have hmemL : ∀ d, d ∈ L ↔ d ∣ k := by
    intro d
    rw [hLdef, Finset.mem_sort, Nat.mem_divisors]
    omega
  have hpw : L.Pairwise (· ≤ ·) := k.divisors.pairwise_sort _
  have hndL : L.Nodup := Finset.sort_nodup _ _
  have h1m : (1 : ℕ) ∈ L := (hmemL 1).2 (one_dvd _)
  have hpm : p ∈ L := (hmemL p).2 hpd
  have hqm : q ∈ L := (hmemL q).2 qdvd
  have hkm : k ∈ L := (hmemL k).2 (dvd_refl _)
  have pair1 : (1, p) ∈ L.zip L.tail := by
    refine mem_zip_of_sorted hpw hndL h1m hpm hp1 ?_
    intro z hz hz1
    have hzd : z ∣ k := (hmemL z).1 hz
    exact hpdef ▸ Nat.minFac_le_of_dvd (by omega) hzd
  have pair2 : (q, k) ∈ L.zip L.tail := by
    refine mem_zip_of_sorted hpw hndL hqm hkm qltk ?_
    intro z hz hzq
    have hzd : z ∣ k := (hmemL z).1 hz
    rcases Nat.lt_or_ge z k with h | h
    · have := qle z hzd h
      omega
    · omega
  set CP := L.zip L.tail with hCP
  show 3 ≤ 1 + CP.countP (fun pr : ℕ × ℕ => Odd pr.2 ∧ pr.2 ≥ 2 * pr.1)
  have hk2q : 2 * q ≤ k := by
    have h : q * 2 ≤ q * p := Nat.mul_le_mul_left q (show 2 ≤ p by omega)
    rw [Nat.mul_comm 2 q]
    rw [hkpq, Nat.mul_comm p q]
    exact h
  have mem1 : ((1 : ℕ), p) ∈ CP.filter (fun pr : ℕ × ℕ => Odd pr.2 ∧ pr.2 ≥ 2 * pr.1) :=
    List.mem_filter.2 ⟨pair1, by
      simp only [decide_eq_true_eq]
      exact ⟨podd, by omega⟩⟩
  have mem2 : (q, k) ∈ CP.filter (fun pr : ℕ × ℕ => Odd pr.2 ∧ pr.2 ≥ 2 * pr.1) :=
    List.mem_filter.2 ⟨pair2, by
      simp only [decide_eq_true_eq]
      exact ⟨kodd, hk2q⟩⟩
  rw [List.countP_eq_length_filter]
  cases hl : (CP.filter (fun pr : ℕ × ℕ => Odd pr.2 ∧ pr.2 ≥ 2 * pr.1)).length with
  | zero =>
    rw [List.length_eq_zero_iff] at hl
    rw [hl] at mem1
    simp at mem1
  | succ n =>
    match n with
    | zero =>
      obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hl
      have hu1 : ((1 : ℕ), p) = u := List.mem_singleton.1 (hu ▸ mem1)
      have hu2 : (q, k) = u := List.mem_singleton.1 (hu ▸ mem2)
      rw [← hu1] at hu2
      have hcontra : q = 1 := congrArg Prod.fst hu2
      omega
    | succ m =>
      omega
