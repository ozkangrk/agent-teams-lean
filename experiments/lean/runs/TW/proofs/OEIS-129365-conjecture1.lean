import FormalConjectures.OEIS.«129365»

/-!
# Proof of OEIS A129365 conjecture1

`(∏ k ∈ [1,n], (n/k)!^k) ∣ (∏_{j,k ∈ [1,n]} gcd j k)`.

For a prime `p`, decompose both sides over `e` (power of `p`):
- LHS: `v_p((n/k)!) = ∑_{e ≥ 1} ⌊(n/k)/p^e⌋` (Legendre), and `⌊⌊n/k⌋/p^e⌋ = ⌊(n/p^e)/k⌋`.
- RHS: `v_p(gcd j k) = #{e ≥ 1 : p^e ∣ gcd j k}` = `#{e : p^e ∣ j} `cross` #{e : p^e ∣ k}`.
Per `e`, LHS contributes `∑_k k·⌊m/k⌋ ≤ m·m` (as `k·⌊m/k⌋ ≤ m` and terms vanish for `k > m`),
while RHS contributes `(n/p^e)·(n/p^e)`.
-/

private lemma lt_pow_of_le {n p : ℕ} (hp : p.Prime) {m : ℕ} (hm : m ≤ n) : m < p ^ n :=
  calc m ≤ n := hm
    _ < 2 ^ n := Nat.lt_two_pow_self
    _ ≤ p ^ n := Nat.pow_le_pow_left hp.two_le n

private lemma gcd_pos_of_pos_left {j k : ℕ} (hj : 0 < j) : 0 < Nat.gcd j k := by
  by_contra hc
  have h0 : Nat.gcd j k = 0 := by omega
  rw [Nat.gcd_eq_zero_iff] at h0
  omega

private lemma card_filter_eq_sum_ite {s : Finset ℕ} {P : ℕ → Prop} [DecidablePred P] :
    (Finset.filter P s).card = ∑ x ∈ s, (if P x then 1 else 0) := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma card_filter_dvd_Icc {n d : ℕ} (hd : 0 < d) :
    (Finset.filter (Dvd.dvd d) (Finset.Icc 1 n)).card = n / d := by
  have hset : (Finset.Icc 1 n).filter (fun j => d ∣ j)
      = (Finset.Ioc 0 n).filter (fun j => d ∣ j) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h1, h3⟩
      rw [Finset.mem_Icc] at h1
      exact ⟨Finset.mem_Ioc.mpr ⟨by omega, h1.2⟩, h3⟩
    · rintro ⟨h1, h3⟩
      rw [Finset.mem_Ioc] at h1
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, h1.2⟩, h3⟩
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div]

private lemma ind_gcd {d j c : ℕ} :
    (if d ∣ Nat.gcd j c then 1 else 0)
      = (if d ∣ j then 1 else 0) * (if d ∣ c then 1 else 0) := by
  by_cases h1 : d ∣ j <;> by_cases h2 : d ∣ c
  · simp [h1, h2, Nat.dvd_gcd]
  · rw [if_neg (fun hg => h2 (Nat.dvd_trans hg (Nat.gcd_dvd_right j c))), if_pos h1, if_neg h2,
      mul_zero]
  · rw [if_neg (fun hg => h1 (Nat.dvd_trans hg (Nat.gcd_dvd_left j c))), if_neg h1, if_pos h2,
      zero_mul]
  · rw [if_neg (fun hg => h1 (Nat.dvd_trans hg (Nat.gcd_dvd_left j c))), if_neg h1, if_neg h2,
      zero_mul]

theorem swarm_proof (n : ℕ) (hn : 0 < n) :
    ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ∣
      ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) := by
  have hmem : ∀ x ∈ Finset.Icc 1 n, 0 < x := fun _ hx => (Finset.mem_Icc.mp hx).1
  have hL : ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ≠ 0 :=
    (Finset.prod_pos fun _ _ => Nat.pow_pos (Nat.factorial_pos (n / _))).ne'
  have hR : ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) ≠ 0 :=
    (Finset.prod_pos fun j hj =>
      Finset.prod_pos fun k _ => gcd_pos_of_pos_left (hmem j hj)).ne'
  rw [← Nat.factorization_le_iff_dvd hL hR, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · -- LHS factorization at p, pushed to ∑_e ∑_k
    have hLp : ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k).factorization p
        = ∑ e ∈ Finset.Ico 1 n, ∑ k ∈ Finset.Icc 1 n, k * ((n / k) / p ^ e) := by
      rw [Nat.factorization_prod_apply (fun _ _ => (Nat.pow_pos (Nat.factorial_pos _)).ne')]
      have per : ∀ k ∈ Finset.Icc 1 n, ((n / k).factorial ^ k).factorization p
          = k * ∑ e ∈ Finset.Ico 1 n, ((n / k) / p ^ e) := by
        intro k hk
        have hkb := Finset.mem_Icc.mp hk
        have hnk0 : 0 < n / k := Nat.div_pos hkb.2 hkb.1
        have h1 : n / k < p ^ n :=
          lt_of_le_of_lt (Nat.div_le_self n k) (lt_pow_of_le hp (le_refl n))
        have hb : Nat.log p (n / k) < n :=
          (Nat.log_lt_iff_lt_pow hp.one_lt (Nat.ne_of_gt hnk0)).mpr h1
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          Nat.factorization_factorial hp hb]
      rw [Finset.sum_congr rfl per]
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    -- RHS factorization at p, as ∑_e (n/p^e)²
    have hRp : ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization p
        = ∑ e ∈ Finset.Ico 1 n, ((n / p ^ e) * (n / p ^ e)) := by
      rw [Nat.factorization_prod_apply (fun j hj =>
        (Finset.prod_pos fun k _ => gcd_pos_of_pos_left (hmem j hj)).ne')]
      have per : ∀ j ∈ Finset.Icc 1 n,
          ((Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization p
            = ∑ k ∈ Finset.Icc 1 n, (Nat.gcd j k).factorization p :=
        fun j hj => Nat.factorization_prod_apply
          (fun k hk => (gcd_pos_of_pos_left (hmem j hj)).ne')
      rw [Finset.sum_congr rfl per]
      have step1 : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
          (Nat.gcd j k).factorization p
            = ∑ e ∈ Finset.Ico 1 n, (if p ^ e ∣ Nat.gcd j k then 1 else 0) := by
        intro j hj k hk
        have hj1 : 0 < j := hmem j hj
        have hgcdn : Nat.gcd j k ≤ n :=
          (Nat.le_of_dvd hj1 (Nat.gcd_dvd_left j k)).trans (Finset.mem_Icc.mp hj).2
        rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (gcd_pos_of_pos_left hj1)
          (lt_pow_of_le hp hgcdn), card_filter_eq_sum_ite]
      rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => step1 j hj k hk))]
      have swapke : ∀ j ∈ Finset.Icc 1 n,
          ∑ k ∈ Finset.Icc 1 n, ∑ e ∈ Finset.Ico 1 n, (if p ^ e ∣ Nat.gcd j k then 1 else 0)
            = ∑ e ∈ Finset.Ico 1 n, ∑ k ∈ Finset.Icc 1 n,
                (if p ^ e ∣ Nat.gcd j k then 1 else 0) :=
        fun _ _ => Finset.sum_comm
      rw [Finset.sum_congr rfl swapke, Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [ind_gcd]
      rw [← Finset.sum_mul_sum, ← card_filter_eq_sum_ite,
        card_filter_dvd_Icc (Nat.pow_pos hp.pos)]
    -- per-e key bound
    have key : ∀ e ∈ Finset.Ico 1 n,
        ∑ k ∈ Finset.Icc 1 n, k * ((n / k) / p ^ e) ≤ (n / p ^ e) * (n / p ^ e) := by
      intro e _
      have hmn : n / p ^ e ≤ n := Nat.div_le_self n (p ^ e)
      have hdiv : ∀ k : ℕ, (n / k) / p ^ e = (n / p ^ e) / k := fun k => by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm k (p ^ e), ← Nat.div_div_eq_div_mul]
      simp_rw [hdiv]
      have hset : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hset, Finset.sum_Ico_eq_sum_range]
      show ∑ i ∈ Finset.range (n + 1 - 1),
          (fun i => (1 + i) * ((n / p ^ e) / (1 + i))) i
        ≤ (n / p ^ e) * (n / p ^ e)
      rw [show n + 1 - 1 = n from by omega]
      have hsplit : ∑ i ∈ Finset.range n, (fun i => (1 + i) * ((n / p ^ e) / (1 + i))) i
          = ∑ i ∈ Finset.range (n / p ^ e), (fun i => (1 + i) * ((n / p ^ e) / (1 + i))) i
            + ∑ i ∈ Finset.Ico (n / p ^ e) n, (fun i => (1 + i) * ((n / p ^ e) / (1 + i))) i :=
        (Finset.sum_range_add_sum_Ico _ hmn).symm
      rw [hsplit]
      have hzero : ∑ i ∈ Finset.Ico (n / p ^ e) n,
          (fun i => (1 + i) * ((n / p ^ e) / (1 + i))) i = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hlt : n / p ^ e < 1 + i := by
          have := (Finset.mem_Ico.mp hi).1; omega
        show (1 + i) * ((n / p ^ e) / (1 + i)) = 0
        rw [Nat.div_eq_of_lt hlt, mul_zero]
      rw [hzero, add_zero]
      calc ∑ i ∈ Finset.range (n / p ^ e), (fun i => (1 + i) * ((n / p ^ e) / (1 + i))) i
          ≤ ∑ i ∈ Finset.range (n / p ^ e), (n / p ^ e) :=
            Finset.sum_le_sum fun i _ => Nat.mul_div_le (n / p ^ e) (1 + i)
        _ = (n / p ^ e) * (n / p ^ e) := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [hLp, hRp]
    exact Finset.sum_le_sum key
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _
