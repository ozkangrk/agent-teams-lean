import FormalConjectures.OEIS.«129365»

/-! Swarm proof for OEIS A129365 conjecture1:
`∏_{k≤n} (n/k)!^k ∣ ∏_{j≤n} ∏_{k≤n} gcd j k`, via p-adic valuations. -/

namespace S129365

open Finset Nat Finsupp

set_option maxHeartbeats 512000

/-- Count multiples of q in `Icc 1 n` equals `n / q`. -/
theorem count_mul (n : ℕ) (hn : 0 < n) (q : ℕ) (hq : 0 < q) :
    ∑ k ∈ Finset.Icc 1 n, (if q ∣ k then 1 else 0) = n / q := by
  have hmap : (Finset.Icc 1 n).filter (fun k => q ∣ k)
      = (Finset.Icc 1 (n / q)).image (fun t => t * q) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨k / q, ⟨?_, Nat.div_le_div_right h2⟩,
        show k / q * q = k by rw [Nat.mul_comm]; exact Nat.mul_div_cancel' h3⟩
      have hqk : q ≤ k := Nat.le_of_dvd (by omega) h3
      have := Nat.div_pos hqk hq
      omega
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨⟨by have := Nat.mul_pos ht1 hq; omega, ?_⟩, t, Nat.mul_comm _ _⟩
      calc t * q = q * t := Nat.mul_comm t q
        _ ≤ q * (n / q) := Nat.mul_le_mul_left q ht2
        _ = n / q * q := Nat.mul_comm _ _
        _ ≤ n := Nat.div_mul_le_self n q
  have h1 : ∑ k ∈ Finset.Icc 1 n, (if q ∣ k then 1 else 0)
      = #((Finset.Icc 1 n).filter (fun k => q ∣ k)) := by
    rw [← Finset.sum_filter, Finset.sum_const]; simp
  have h2 : #((Finset.Icc 1 n).filter (fun k => q ∣ k)) = n / q := by
    rw [hmap, Finset.card_image_of_injOn
      (fun t1 _ t2 _ h => Nat.eq_of_mul_eq_mul_right hq h), Nat.card_Icc, Nat.add_sub_cancel]
  rw [h1, h2]

theorem swarm_core (n : ℕ) (hn : 0 < n) :
    ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ∣
      ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) := by
  set L : ℕ := (Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k with hLdef
  set R : ℕ := (Finset.Icc 1 n).prod fun j =>
    (Finset.Icc 1 n).prod fun k => Nat.gcd j k with hRdef
  have hRne : R ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    have hj1 : 0 < j := by have := Finset.mem_Icc.mp hj; omega
    exact Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ hj1)
  have hLne : L ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ =>
      pow_ne_zero _ (Nat.factorial_ne_zero _)
  refine (Nat.factorization_le_iff_dvd hLne hRne).mp ?_
  rw [Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    have hLval : L.factorization p
        = ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n+1), k * ((n / k) / p ^ i) := by
      rw [hLdef, Nat.factorization_prod (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _)),
        Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : ((n / k).factorial ^ k).factorization p
          = k * ((n / k).factorial).factorization p := by
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      rw [h1, Nat.factorization_def _ hp,
        padicValNat_factorial (b := n + 1)
          (by have h1 := Nat.log_le_self p (n / k); have h2 := Nat.div_le_self n k; omega),
        Finset.mul_sum]
    have hLle : L.factorization p ≤ ∑ i ∈ Finset.Ico 1 (n+1), (n / p ^ i) * (n / p ^ i) := by
      rw [hLval, Finset.sum_comm]
      refine Finset.sum_le_sum fun i _ => ?_
      set q := p ^ i with hqdef
      have hq0 : 0 < q := pow_pos hp.pos _
      have hkey : ∀ k ∈ Finset.Icc 1 n,
          k * ((n / k) / q) ≤ (if k ≤ n / q then n / q else 0) := by
        intro k _
        by_cases hkm : k ≤ n / q
        · rw [if_pos hkm]
          have hAq : k * ((n / k) / q) * q ≤ n := by
            rw [Nat.div_div_eq_div_mul]
            have hd := Nat.div_mul_le_self n (k * q)
            calc k * (n / (k * q)) * q = (n / (k * q)) * (k * q) := by ring
              _ ≤ n := hd
          exact Nat.le_div_iff_mul_le hq0 |>.mpr hAq
        · rw [if_neg hkm]
          have hlt2 : n / q < k := lt_of_not_ge hkm
          have hlt : n < k * q := by
            calc n < q * (n / q + 1) := Nat.lt_mul_div_succ _ hq0
              _ ≤ q * k := Nat.mul_le_mul_left _ (by omega)
              _ = k * q := Nat.mul_comm _ _
          have hnk : n / k < q := Nat.div_lt_of_lt_mul (by omega)
          rw [Nat.div_eq_of_lt hnk]
          omega
      calc ∑ k ∈ Finset.Icc 1 n, k * ((n / k) / q)
          ≤ ∑ k ∈ Finset.Icc 1 n, (if k ≤ n / q then n / q else 0) :=
            Finset.sum_le_sum hkey
        _ = ((Finset.Icc 1 n).filter (fun k => k ≤ n / q)).sum fun _ => n / q := by
            rw [← Finset.sum_filter]
        _ = (Finset.Icc 1 (n / q)).sum fun _ => n / q := by
            congr 1
            ext k
            simp only [Finset.mem_filter, Finset.mem_Icc]
            constructor
            · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨⟨h1, Nat.le_trans h2 (Nat.div_le_self n q)⟩, h2⟩
        _ = (n / q) * (n / q) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]; simp
    have hRval : R.factorization p
        = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (Nat.gcd j k).factorization p := by
      rw [hRdef, Nat.factorization_prod (fun j hj =>
          Finset.prod_ne_zero_iff.mpr fun k _ =>
            Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (by
              have := Finset.mem_Icc.mp hj; omega))),
        Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.factorization_prod (fun k hk =>
          Nat.ne_of_gt (Nat.gcd_pos_of_pos_right _ (by
            have := Finset.mem_Icc.mp hk; omega))),
        Finsupp.finsetSum_apply]
    have keypair : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
        ∑ i ∈ Finset.Ico 1 (n+1), (if p ^ i ∣ Nat.gcd j k then 1 else 0)
          ≤ (Nat.gcd j k).factorization p := by
      intro j hj k hk
      have hj1 : 0 < j := by have := Finset.mem_Icc.mp hj; omega
      have hg0 : Nat.gcd j k ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ hj1)
      have hsub : (Finset.Ico 1 (n+1)).filter (fun i => p ^ i ∣ Nat.gcd j k)
          ⊆ Finset.Ico 1 ((Nat.gcd j k).factorization p + 1) := by
        intro i hi
        have hiv : p ^ i ∣ Nat.gcd j k := (Finset.mem_filter.mp hi).2
        have h3 : i ≤ (Nat.gcd j k).factorization p :=
          (Nat.Prime.pow_dvd_iff_le_factorization hp hg0).mp hiv
        simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
        omega
      have hsumite : ∑ i ∈ Finset.Ico 1 (n+1), (if p ^ i ∣ Nat.gcd j k then 1 else 0)
          = #((Finset.Ico 1 (n+1)).filter (fun i => p ^ i ∣ Nat.gcd j k)) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
      rw [hsumite]
      calc #((Finset.Ico 1 (n+1)).filter (fun i => p ^ i ∣ Nat.gcd j k))
          ≤ #(Finset.Ico 1 ((Nat.gcd j k).factorization p + 1)) := Finset.card_mono hsub
        _ = (Nat.gcd j k).factorization p := by rw [Nat.card_Ico]; omega
    have step1 : ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n+1),
            (if p ^ i ∣ Nat.gcd j k then 1 else 0)
          = ∑ i ∈ Finset.Ico 1 (n+1), ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
            (if p ^ i ∣ Nat.gcd j k then 1 else 0) := by
      calc ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n+1),
              (if p ^ i ∣ Nat.gcd j k then 1 else 0)
          = ∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n+1), ∑ k ∈ Finset.Icc 1 n,
              (if p ^ i ∣ Nat.gcd j k then 1 else 0) := by
              refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
        _ = ∑ i ∈ Finset.Ico 1 (n+1), ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
              (if p ^ i ∣ Nat.gcd j k then 1 else 0) := Finset.sum_comm
    have step2 : ∀ i ∈ Finset.Ico 1 (n+1),
        ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (if p ^ i ∣ Nat.gcd j k then 1 else 0)
          = (n / p ^ i) * (n / p ^ i) := by
      intro i _
      have hq0 : 0 < p ^ i := pow_pos hp.pos _
      have hite : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
          (if p ^ i ∣ Nat.gcd j k then 1 else 0)
            = (if p ^ i ∣ j then 1 else 0) * (if p ^ i ∣ k then 1 else 0) := by
        intro j _ k _
        have hiff : (p ^ i ∣ Nat.gcd j k) ↔ (p ^ i ∣ j ∧ p ^ i ∣ k) := by
          constructor
          · intro h
            exact ⟨h.trans (Nat.gcd_dvd_left j k), h.trans (Nat.gcd_dvd_right j k)⟩
          · rintro ⟨h1, h2⟩
            exact Nat.dvd_gcd h1 h2
        by_cases h1 : p ^ i ∣ j
        · by_cases h2 : p ^ i ∣ k
          · rw [if_pos (hiff.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2]
          · rw [if_neg (fun hc => h2 (hiff.mp hc).2), if_pos h1, if_neg h2, mul_zero]
        · by_cases h2 : p ^ i ∣ k
          · rw [if_neg (fun hc => h1 (hiff.mp hc).1), if_neg h1, if_pos h2, zero_mul]
          · rw [if_neg (fun hc => h1 (hiff.mp hc).1), if_neg h1, if_neg h2, zero_mul]
      have hmain : ∀ j ∈ Finset.Icc 1 n,
          ∑ k ∈ Finset.Icc 1 n, (if p ^ i ∣ Nat.gcd j k then 1 else 0)
            = (if p ^ i ∣ j then 1 else 0) * (n / p ^ i) := by
        intro j hj
        rw [Finset.sum_congr rfl (fun k hk => hite j hj k hk), ← Finset.mul_sum,
          count_mul n hn (p ^ i) hq0]
      calc ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (if p ^ i ∣ Nat.gcd j k then 1 else 0)
          = ∑ j ∈ Finset.Icc 1 n, (if p ^ i ∣ j then 1 else 0) * (n / p ^ i) :=
            Finset.sum_congr rfl (fun j hj => hmain j hj)
        _ = (∑ j ∈ Finset.Icc 1 n, (if p ^ i ∣ j then 1 else 0)) * (n / p ^ i) := by
            rw [Finset.sum_mul]
        _ = (n / p ^ i) * (n / p ^ i) := by rw [count_mul n hn (p ^ i) hq0]
    calc L.factorization p
        ≤ ∑ i ∈ Finset.Ico 1 (n+1), (n / p ^ i) * (n / p ^ i) := hLle
      _ ≤ ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (Nat.gcd j k).factorization p := by
          rw [Finset.sum_congr rfl (fun i hi => (step2 i hi).symm), ← step1]
          exact Finset.sum_le_sum fun j hj =>
            Finset.sum_le_sum fun k hk => keypair j hj k hk
      _ = R.factorization p := hRval.symm
  · have h0 : L.factorization p = 0 := by
      have h1 : p ∉ L.factorization.support := by
        intro hmem
        rw [Nat.support_factorization] at hmem
        exact hp (Nat.prime_of_mem_primeFactors hmem)
      exact Finsupp.notMem_support_iff.mp h1
    omega

end S129365

theorem swarm_proof : ∀ (n : ℕ) (hn : 0 < n),
    ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ∣
      ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) :=
  fun n hn => S129365.swarm_core n hn
