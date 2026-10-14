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


/-! ## conjecture2: integrality refinement -/

/-- Sum of `k * (m / k)` over `Icc 1 n` equals the same over `Icc 1 m` (zero outside). -/
theorem sum_restrict (n m : ℕ) (hm : m ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, k * (m / k) = ∑ k ∈ Finset.Icc 1 m, k * (m / k) := by
  have hsub : (Finset.Icc 1 m) ⊆ (Finset.Icc 1 n) := by
    intro x hx
    have h := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨h.1, Nat.le_trans h.2 hm⟩
  have hzero : ∀ x ∈ Finset.Icc 1 n, x ∉ Finset.Icc 1 m → x * (m / x) = 0 := by
    intro x hx hxn
    have h1 := Finset.mem_Icc.mp hx
    have hlt : m < x := by
      by_contra hc
      exact hxn (Finset.mem_Icc.mpr ⟨h1.1, by omega⟩)
    rw [Nat.div_eq_of_lt hlt, mul_zero]
  exact (Finset.sum_subset hsub hzero).symm

/-- Pointwise bound: `∑ k ≤ n, k * (m / k) ≤ m * m`. -/
theorem sum_le_sq (n : ℕ) (m : ℕ) (hmn : m ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, k * (m / k) ≤ m * m := by
  have hkey : ∀ k ∈ Finset.Icc 1 n, k * (m / k) ≤ (if k ≤ m then m else 0) := by
    intro k _
    by_cases hkm : k ≤ m
    · rw [if_pos hkm]
      calc k * (m / k) = (m / k) * k := Nat.mul_comm _ _
        _ ≤ m := Nat.div_mul_le_self m k
    · rw [if_neg hkm, Nat.div_eq_of_lt (by omega), mul_zero]
  calc ∑ k ∈ Finset.Icc 1 n, k * (m / k)
      ≤ ∑ k ∈ Finset.Icc 1 n, (if k ≤ m then m else 0) := Finset.sum_le_sum hkey
    _ = ((Finset.Icc 1 n).filter (fun k => k ≤ m)).sum fun _ => m := by
        rw [← Finset.sum_filter]
    _ = (Finset.Icc 1 m).sum fun _ => m := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, Nat.le_trans h2 hmn⟩, h2⟩
    _ = m * m := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]; simp

/-- For `m ≥ 3` the bound is strict by one. -/
theorem gpos (n : ℕ) {m : ℕ} (hm : m ≤ n) (h3 : 3 ≤ m) :
    ∑ k ∈ Finset.Icc 1 n, k * (m / k) + 1 ≤ m * m := by
  rw [sum_restrict n m hm]
  have hset : Finset.Icc 1 m = insert 1 (insert (m-1) (insert m (Finset.Ico 2 (m-1)))) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hset]
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega),
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ico]; omega)]
  have hmid : m / (m - 1) * (m - 1) ≤ m := Nat.div_mul_le_self m (m - 1)
  have hcomm : (m - 1) * (m / (m - 1)) = m / (m - 1) * (m - 1) := Nat.mul_comm _ _
  have hmid2 : m / (m - 1) ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ m / (m - 1) := by omega
    have h3' : (m - 1) * 2 ≤ (m - 1) * (m / (m - 1)) := Nat.mul_le_mul_left _ h2
    have h4 : 2 * (m - 1) = (m - 1) + (m - 1) := by ring
    omega
  have h2b : (m - 1) * (m / (m - 1)) ≤ m - 1 :=
    Nat.le_trans (Nat.mul_le_mul_left _ hmid2) (by omega)
  have hb3 : m * (m / m) ≤ m := by
    rw [Nat.div_self (by omega)]
    omega
  have hb1 : 1 * (m / 1) ≤ m := by rw [Nat.div_one]; omega
  have hrest : ∀ k ∈ Finset.Ico 2 (m-1), k * (m / k) ≤ m := fun k _ => by
    calc k * (m / k) = (m / k) * k := Nat.mul_comm _ _
      _ ≤ m := Nat.div_mul_le_self m k
  have hrestsum : ∑ k ∈ Finset.Ico 2 (m-1), k * (m / k) ≤ m * (m - 3) := by
    have h1 : ∑ k ∈ Finset.Ico 2 (m-1), k * (m / k) ≤ ∑ k ∈ Finset.Ico 2 (m-1), m :=
      Finset.sum_le_sum hrest
    have h2 : ∑ k ∈ Finset.Ico 2 (m-1), m = m * #(Finset.Ico 2 (m-1)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm, Nat.cast_id]
    rw [h2] at h1
    have h3c : #(Finset.Ico 2 (m-1)) = m - 3 := by rw [Nat.card_Ico]; omega
    rw [h3c] at h1
    exact h1
  have hring : m * (m - 3) = m * m - 3 * m := by rw [Nat.mul_sub, Nat.mul_comm m 3]
  have hplus : m * (m - 3) + 3 * m = m * m := by
    rw [Nat.mul_comm 3 m, ← Nat.mul_add, Nat.sub_add_cancel h3]
  have hcomb : ∑ k ∈ Finset.Ico 2 (m-1), k * (m / k) + 3 * m ≤ m * m :=
    (Nat.add_le_add_right hrestsum (3 * m)).trans_eq hplus
  have hm0 : 0 < m := by omega
  rw [Nat.div_one, Nat.div_self hm0]
  omega

/-- For `m ≤ 2` equality holds. -/
theorem gzero (n : ℕ) {m : ℕ} (hm : m ≤ n) (hm2 : m ≤ 2) :
    ∑ k ∈ Finset.Icc 1 n, k * (m / k) = m * m := by
  rw [sum_restrict n m hm]
  rcases m with _ | _ | _ | m4
  · simp
  · decide
  · decide
  · omega

/-- Exact p-adic count for `g ≤ n`. -/
theorem pair_count (n : ℕ) {p g : ℕ} (hp : p.Prime) (hg0 : g ≠ 0) (hg : g ≤ n) :
    padicValNat p g = #((Finset.Ico 1 (n+1)).filter (fun i => p ^ i ∣ g)) := by
  have h1 : (Finset.Ico 1 (n+1)).filter (fun i => p ^ i ∣ g)
      ⊆ Finset.Ico 1 (padicValNat p g + 1) := by
    intro i hi
    have hiv : p ^ i ∣ g := (Finset.mem_filter.mp hi).2
    have h3 : i ≤ padicValNat p g := (pow_dvd_iff_le_padicValNat hp.ne_one hg0).mp hiv
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
    omega
  have h2 : Finset.Ico 1 (padicValNat p g + 1)
      ⊆ (Finset.Ico 1 (n+1)).filter (fun i => p ^ i ∣ g) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
    have hle : i ≤ padicValNat p g := by omega
    have hiv : p ^ i ∣ g := (pow_dvd_iff_le_padicValNat hp.ne_one hg0).mpr hle
    have hvs : padicValNat p g ≤ g := padicValNat_le_self g
    constructor
    · omega
    · exact hiv
  have e1 := Finset.card_mono h1
  have e2 := Finset.card_mono h2
  have ec : #(Finset.Ico 1 (padicValNat p g + 1)) = padicValNat p g := by
    rw [Nat.card_Ico]; omega
  omega

theorem swarm_core2 (n : ℕ) (hn : 0 < n) (p : ℕ) (hp : p.Prime) :
    (∃ m : ℕ, OeisA129365.a n = m ∧ p ∣ m) ↔ p ≤ n / 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set D₁ : ℕ := (Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k with hD
  set N₁ : ℕ := (Finset.Icc 1 n).prod fun j =>
    (Finset.Icc 1 n).prod fun k => Nat.gcd j k with hN
  have hdvd1 : D₁ ∣ N₁ := swarm_core n hn
  have hD1ne : D₁ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _)
  have hN1ne : N₁ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj =>
      Finset.prod_ne_zero_iff.mpr fun k _ =>
        Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (by have := Finset.mem_Icc.mp hj; omega))
  have hLv : D₁.factorization p
      = ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n+1), k * ((n / k) / p ^ i) := by
    rw [hD, Nat.factorization_prod (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _)),
      Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : ((n / k).factorial ^ k).factorization p
        = k * ((n / k).factorial).factorization p := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [h1, Nat.factorization_def _ hp,
      padicValNat_factorial (b := n + 1)
        (by have h1 := Nat.log_le_self p (n / k); have h2 := Nat.div_le_self n k; omega),
      Finset.mul_sum]
  have hRv : N₁.factorization p
      = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (Nat.gcd j k).factorization p := by
    rw [hN, Nat.factorization_prod (fun j hj =>
        Finset.prod_ne_zero_iff.mpr fun k _ =>
          Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ (by have := Finset.mem_Icc.mp hj; omega))),
      Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.factorization_prod (fun k hk =>
        Nat.ne_of_gt (Nat.gcd_pos_of_pos_right _ (by have := Finset.mem_Icc.mp hk; omega))),
      Finsupp.finsetSum_apply]
  have hpairEq : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
      (Nat.gcd j k).factorization p
        = ∑ i ∈ Finset.Ico 1 (n+1), (if p ^ i ∣ Nat.gcd j k then 1 else 0) := by
    intro j hj k hk
    have hj1 : 0 < j := by have := Finset.mem_Icc.mp hj; omega
    have hg0 : Nat.gcd j k ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left _ hj1)
    have hgn : Nat.gcd j k ≤ n :=
      Nat.le_trans (Nat.gcd_le_left k hj1) (Finset.mem_Icc.mp hj).2
    have hite : ∑ i ∈ Finset.Ico 1 (n+1), (if p ^ i ∣ Nat.gcd j k then 1 else 0)
        = #((Finset.Ico 1 (n+1)).filter (fun i => p ^ i ∣ Nat.gcd j k)) := by
      rw [← Finset.sum_filter, Finset.sum_const]; simp
    rw [Nat.factorization_def _ hp, pair_count n hp hg0 hgn, hite]
  have hswap : ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n+1),
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
  have hev : ∀ i ∈ Finset.Ico 1 (n+1),
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
  have hRv2 : N₁.factorization p
      = ∑ i ∈ Finset.Ico 1 (n+1), (n / p ^ i) * (n / p ^ i) := by
    rw [hRv]
    refine Eq.trans (Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun k hk => hpairEq j hj k hk) ?_
    rw [hswap]
    exact Finset.sum_congr rfl (fun i hi => hev i hi)
  have hterm : ∀ k ∈ Finset.Icc 1 n, ∀ i ∈ Finset.Ico 1 (n+1),
      k * ((n / k) / p ^ i) = k * ((n / p ^ i) / k) := by
    intro k _ i _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm (p ^ i) k]
  have hLv2 : D₁.factorization p
      = ∑ i ∈ Finset.Ico 1 (n+1), ∑ k ∈ Finset.Icc 1 n, k * ((n / p ^ i) / k) := by
    rw [hLv, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => hterm k hk i hi
  have ha : OeisA129365.a n = ((N₁ : ℚ) / (D₁ : ℚ)) := by
    simp [OeisA129365.a, hN, hD]
  have hmval : OeisA129365.a n = ((N₁ / D₁ : ℕ) : ℚ) := by
    rw [ha, Nat.cast_div hdvd1 (by exact_mod_cast hD1ne)]
  have keydvd : p ∣ N₁ / D₁ ↔ p * D₁ ∣ N₁ := by
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      calc N₁ = D₁ * (N₁ / D₁) := (Nat.mul_div_cancel' hdvd1).symm
        _ = D₁ * (p * c) := by rw [← hc]
        _ = p * D₁ * c := by ring
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [show N₁ = D₁ * (p * c) from by rw [hc]; ring]
      exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hD1ne)
  constructor
  · rintro ⟨m, ham, hpm⟩
    by_contra hcon
    push_neg at hcon
    have hmN : m = N₁ / D₁ := by
      have hq : ((m : ℚ)) = ((N₁ / D₁ : ℕ) : ℚ) := by rw [← hmval]; exact ham.symm
      exact_mod_cast hq
    have hd : p * D₁ ∣ N₁ := keydvd.mp (hmN ▸ hpm)
    have h1 : p * D₁ ≠ 0 := Nat.mul_ne_zero hp.ne_zero hD1ne
    have hle := (Nat.factorization_le_iff_dvd h1 hN1ne).mpr hd
    rw [Finsupp.le_def] at hle
    have hpp := hle p
    have hfpp : (p * D₁).factorization p = 1 + D₁.factorization p := by
      rw [Nat.factorization_mul hp.ne_zero hD1ne, Finsupp.add_apply, hp.factorization,
        Finsupp.single_apply, if_pos rfl]
    rw [hfpp] at hpp
    have h5 : ¬(p * 3 ≤ n) := by
      intro hc
      have h7 : p ≤ n / 3 := (Nat.le_div_iff_mul_le (show 0 < 3 by omega)).mpr hc
      omega
    have h6 : p * 3 = 3 * p := Nat.mul_comm _ _
    have hm1 : n / p < 3 :=
      Nat.div_lt_of_lt_mul (show n < p * 3 by rw [Nat.mul_comm]; omega)
    have hmile : ∀ i ∈ Finset.Ico 1 (n+1), n / p ^ i ≤ 2 := by
      intro i hi
      have hpi : p ≤ p ^ i :=
        Nat.le_trans (Nat.le_of_eq (Nat.pow_one p).symm)
          (Nat.pow_le_pow_right hp.one_le (Finset.mem_Ico.mp hi).1)
      exact Nat.le_trans (Nat.div_le_div_left hpi hp.pos) (by have := hm1; omega)
    have hsq : ∑ i ∈ Finset.Ico 1 (n+1), (n / p ^ i) * (n / p ^ i)
        = ∑ i ∈ Finset.Ico 1 (n+1), ∑ k ∈ Finset.Icc 1 n, k * ((n / p ^ i) / k) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← gzero n (Nat.div_le_self n _) (hmile i hi)]
    rw [hLv2] at hpp
    rw [hRv2] at hpp
    rw [hsq] at hpp
    omega
  · intro hle
    refine ⟨N₁ / D₁, hmval, ?_⟩
    refine keydvd.mpr ?_
    have h1 : p * D₁ ≠ 0 := Nat.mul_ne_zero hp.ne_zero hD1ne
    refine (Nat.factorization_le_iff_dvd h1 hN1ne).mp ?_
    rw [Finsupp.le_def]
    intro q
    by_cases hqp : q = p
    · rw [hqp]
      have hn3 : 3 ≤ n / p := by
        have h5 : p * 3 ≤ n := (Nat.le_div_iff_mul_le (show 0 < 3 by omega)).mp hle
        have h6 : 3 * p ≤ n := by rw [Nat.mul_comm]; exact h5
        exact (Nat.le_div_iff_mul_le hp.pos).mpr h6
      have hI : Finset.Ico 1 (n+1) = insert 1 (Finset.Ico 2 (n+1)) := by
        ext i; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hkey1 : (n / p ^ 1) * (n / p ^ 1)
          ≥ ∑ k ∈ Finset.Icc 1 n, k * ((n / p ^ 1) / k) + 1 := by
        have hq1 : n / p ^ 1 = n / p := by rw [Nat.pow_one]
        have hmp : n / p ≤ n := Nat.div_le_self n p
        rw [hq1]
        exact gpos n hmp hn3
      have hkeyi : ∀ i ∈ Finset.Ico 2 (n+1),
          ∑ k ∈ Finset.Icc 1 n, k * ((n / p ^ i) / k) ≤ (n / p ^ i) * (n / p ^ i) := by
        intro i _
        exact sum_le_sq n (n / p ^ i) (Nat.div_le_self n _)
      have hsum2 : ∑ i ∈ Finset.Ico 2 (n+1), ∑ k ∈ Finset.Icc 1 n, k * ((n / p ^ i) / k)
          ≤ ∑ i ∈ Finset.Ico 2 (n+1), (n / p ^ i) * (n / p ^ i) :=
        Finset.sum_le_sum hkeyi
      have hfpp : (p * D₁).factorization p = 1 + D₁.factorization p := by
        rw [Nat.factorization_mul hp.ne_zero hD1ne, Finsupp.add_apply, hp.factorization,
          Finsupp.single_apply, if_pos rfl]
      rw [hfpp, hRv2, hI, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega),
        hLv2, hI, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
      omega
    · have hqm : D₁.factorization q ≤ N₁.factorization q :=
        Nat.factorization_le_factorization_of_dvd_right hdvd1 hD1ne hN1ne
      rw [Nat.factorization_mul hp.ne_zero hD1ne, Finsupp.add_apply, hp.factorization,
        Finsupp.single_apply, if_neg (Ne.symm hqp), zero_add]
      exact hqm

end S129365

theorem swarm_proof : ∀ (n p : ℕ) (hn : 0 < n) (hp : p.Prime),
    (∃ m : ℕ, OeisA129365.a n = m ∧ p ∣ m) ↔ p ≤ n / 3 :=
  fun n p hn hp => S129365.swarm_core2 n hn p hp
