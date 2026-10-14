import FormalConjectures.OEIS.«129365»

/-!
# Proof of OEIS A129365 conjecture2

`(∃ m : ℕ, a n = m ∧ p ∣ m) ↔ p ≤ n / 3` for `p` prime, where
`a n = (∏_{j,k ∈ [1,n]} gcd j k) / (∏_{k ∈ [1,n]} (n/k)! ^ k)` as a rational.

Key: for every prime `p`, with `P` the gcd product and `Q` the factorial product,
`P.factorization p = Q.factorization p + ∑_{e ∈ [1,n)} T (n / p^e)`,
where `T q = ∑_{k ∈ [1,q]} q % k`.  Indeed, per `e`, with `q := n / p^e`:
`∑_k k * ((n/k)/p^e) = ∑_{k ≤ q} k * (q/k) = q * q − T q`, using `k * (q/k) = q − q % k`.
`T q = 0` for `q ≤ 2` and `1 ≤ T q` for `3 ≤ q` (if `q` odd use `q % 2 = 1`;
if `q = 2m` use `q % (m+1) = m − 1`).  Hence `v_p (a n) ≥ 1 ↔ ∃ e, 3 ≤ n / p^e ↔ p ≤ n / 3`.
-/

open OeisA129365 Finset Nat

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

/-- `T q = ∑_{k ∈ [1,q]} q % k` (the OEIS `b(n)`). -/
private def T (q : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 q, q % k

private lemma T_eq : ∀ q, T q = ∑ k ∈ Finset.Icc 1 q, q % k := fun _ => rfl

private lemma T_le_two : ∀ q, q ≤ 2 → T q = 0 := by
  intro q hq
  interval_cases q <;> decide

private lemma one_le_T : ∀ q, 3 ≤ q → 1 ≤ T q := by
  intro q hq
  rcases Nat.even_or_odd q with ⟨m, rfl⟩ | hodd
  · have hm2 : 2 ≤ m := by omega
    have hmem : m + 1 ∈ Finset.Icc 1 (m + m) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hdiv1 : (m + m) / (m + 1) = 1 := by
      have h1 : 1 ≤ (m + m) / (m + 1) := (Nat.one_le_div_iff (by omega)).mpr (by omega)
      have h2 : (m + m) / (m + 1) < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega
    have hmod : (m + m) % (m + 1) = m - 1 := by
      have h := Nat.div_add_mod (m + m) (m + 1)
      rw [hdiv1] at h
      omega
    have h1 : 1 ≤ (m + m) % (m + 1) := by omega
    have h2 : (m + m) % (m + 1) ≤ ∑ k ∈ Finset.Icc 1 (m + m), (m + m) % k :=
      single_le_sum (fun _ _ => Nat.zero_le _) hmem
    show 1 ≤ T (m + m)
    rw [T_eq]
    omega
  · rcases hodd with ⟨m2, rfl⟩
    have hmem : 2 ∈ Finset.Icc 1 (2 * m2 + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h2 : (2 * m2 + 1) % 2 ≤ ∑ k ∈ Finset.Icc 1 (2 * m2 + 1), (2 * m2 + 1) % k :=
      single_le_sum (fun _ _ => Nat.zero_le _) hmem
    show 1 ≤ T (2 * m2 + 1)
    rw [T_eq]
    omega

private lemma sum_k_mul_add_T (n p e : ℕ) (hp : 2 ≤ p) (he : 1 ≤ e) :
    (∑ k ∈ Finset.Icc 1 n, k * ((n / k) / p ^ e)) + T (n / p ^ e)
      = (n / p ^ e) * (n / p ^ e) := by
  have hpe1 : p ^ 1 ≤ p ^ e := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (by omega)) he
  rw [pow_one] at hpe1
  have hpe : 2 ≤ p ^ e := le_trans hp hpe1
  have hpe0 : 0 < p ^ e := lt_of_lt_of_le (by omega) hpe
  have hqn : n / p ^ e ≤ n := Nat.div_le_self n (p ^ e)
  have hsub : Finset.Icc 1 (n / p ^ e) ⊆ Finset.Icc 1 n :=
    Finset.Icc_subset_Icc (le_refl 1) hqn
  have hval : ∀ k ∈ Finset.Icc 1 (n / p ^ e), (n / k) / p ^ e = (n / p ^ e) / k := by
    intro k _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have hzero : ∀ k ∈ Finset.Icc 1 n, k ∉ Finset.Icc 1 (n / p ^ e) →
      k * ((n / k) / p ^ e) = 0 := by
    intro k hk hkq
    have hkq' : n / p ^ e < k := by
      by_contra hc
      push_neg at hc
      exact hkq (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, hc⟩)
    have hdm : p ^ e * (n / p ^ e) + n % p ^ e = n := Nat.div_add_mod n (p ^ e)
    have hmlt : n % p ^ e < p ^ e := Nat.mod_lt n hpe0
    have hkq2 : n / p ^ e + 1 ≤ k := by omega
    have hdist : p ^ e * (n / p ^ e + 1) = p ^ e * (n / p ^ e) + p ^ e := by ring
    have hmul : p ^ e * (n / p ^ e) + p ^ e ≤ p ^ e * k := by
      have h0 : p ^ e * (n / p ^ e + 1) ≤ p ^ e * k := Nat.mul_le_mul_left (p ^ e) hkq2
      rwa [hdist] at h0
    have hlt : n < p ^ e * k := by omega
    have : n / k < p ^ e := (Nat.div_lt_iff_lt_mul (show 0 < k by omega)).mpr hlt
    rw [Nat.div_eq_of_lt this, mul_zero]
  have hsum : ∑ k ∈ Finset.Icc 1 n, k * ((n / k) / p ^ e)
      = ∑ k ∈ Finset.Icc 1 (n / p ^ e), k * ((n / p ^ e) / k) := by
    rw [← Finset.sum_subset hsub hzero]
    exact Finset.sum_congr rfl fun k hk => by rw [hval k hk]
  have hsplit : ∑ k ∈ Finset.Icc 1 (n / p ^ e), (k * ((n / p ^ e) / k) + (n / p ^ e) % k)
      = (n / p ^ e) * ((Finset.Icc 1 (n / p ^ e)).card) := by
    have hper : ∀ k : ℕ, k ∈ Finset.Icc 1 (n / p ^ e) →
        (k * ((n / p ^ e) / k) + (n / p ^ e) % k) = (n / p ^ e) := by
      intro k _
      have := Nat.div_add_mod (n / p ^ e) k
      omega
    simp_rw [hper]
    rw [Finset.sum_const, smul_eq_mul]
  have hcard : (Finset.Icc 1 (n / p ^ e)).card = n / p ^ e := by simp [Nat.card_Icc]
  show (∑ k ∈ Finset.Icc 1 n, k * ((n / k) / p ^ e)) + ∑ k ∈ Finset.Icc 1 (n / p ^ e), (n / p ^ e) % k = _
  rw [hsum, ← Finset.sum_add_distrib, hsplit, hcard]

private lemma fact_Q (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k).factorization p
      = ∑ e ∈ Finset.Ico 1 n, ∑ k ∈ Finset.Icc 1 n, k * ((n / k) / p ^ e) := by
  have hmem : ∀ x ∈ Finset.Icc 1 n, 0 < x := fun _ hx => (Finset.mem_Icc.mp hx).1
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
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_factorial hp hb]
  rw [Finset.sum_congr rfl per]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private lemma fact_P (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization p
      = ∑ e ∈ Finset.Ico 1 n, ((n / p ^ e) * (n / p ^ e)) := by
  have hmem : ∀ x ∈ Finset.Icc 1 n, 0 < x := fun _ hx => (Finset.mem_Icc.mp hx).1
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

private lemma master (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization p
      = ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k).factorization p
        + ∑ e ∈ Finset.Ico 1 n, T (n / p ^ e) := by
  have hQ := fact_Q n p hn hp
  have hP := fact_P n p hn hp
  have hper : ∀ e ∈ Finset.Ico 1 n,
      (∑ k ∈ Finset.Icc 1 n, k * ((n / k) / p ^ e)) + T (n / p ^ e)
        = (n / p ^ e) * (n / p ^ e) := fun e he =>
    sum_k_mul_add_T n p e (by have := hp.one_lt; omega) ((Finset.mem_Ico.mp he).1)
  have hsum : (∑ e ∈ Finset.Ico 1 n, ∑ k ∈ Finset.Icc 1 n, k * ((n / k) / p ^ e))
      + ∑ e ∈ Finset.Ico 1 n, T (n / p ^ e) = ∑ e ∈ Finset.Ico 1 n, (n / p ^ e) * (n / p ^ e) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hper
  omega

theorem swarm_proof (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    (∃ m : ℕ, a n = m ∧ p ∣ m) ↔ p ≤ n / 3 := by
  have hmem : ∀ x ∈ Finset.Icc 1 n, 0 < x := fun _ hx => (Finset.mem_Icc.mp hx).1
  have hP0 : ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) ≠ 0 :=
    (Finset.prod_pos fun j hj =>
      Finset.prod_pos fun k _ => gcd_pos_of_pos_left (hmem j hj)).ne'
  have hQ0 : ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ≠ 0 :=
    (Finset.prod_pos fun _ _ => Nat.pow_pos (Nat.factorial_pos _)).ne'
  have hmaster := master n p hn hp
  constructor
  · rintro ⟨m, hm, hpm⟩
    by_contra hle
    push_neg at hle
    have hT0 : ∀ e ∈ Finset.Ico 1 n, T (n / p ^ e) = 0 := by
      intro e he
      have he1 : 1 ≤ e := (Finset.mem_Ico.mp he).1
      have hpe1 : p ^ 1 ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
      rw [pow_one] at hpe1
      have hpe : p ≤ p ^ e := hpe1
      have h3 : n < 3 * p := by omega
      have hq2 : n / p ^ e ≤ 2 := by
        have : n / p ^ e < 3 := (Nat.div_lt_iff_lt_mul (Nat.pow_pos hp.pos)).mpr (by omega)
        omega
      exact T_le_two _ hq2
    have hW0 : ∑ e ∈ Finset.Ico 1 n, T (n / p ^ e) = 0 := Finset.sum_eq_zero hT0
    have hPQ : ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization p
        = ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k).factorization p := by
      rw [hmaster, hW0, add_zero]
    have hPmQ : ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k)
        = m * ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) := by
      have hcast : (((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k : ℕ) : ℚ)
          / (((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k : ℕ) : ℚ) = (m : ℚ) := by
        simpa [OeisA129365.a, Nat.cast_prod, Nat.cast_pow] using hm
      have hQne : (((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k : ℕ) : ℚ) ≠ 0 :=
        by exact_mod_cast hQ0
      have hcr := (div_eq_iff hQne).mp hcast
      exact_mod_cast hcr
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hPmQ
      exact hP0 hPmQ
    have hfac : ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization
        = m.factorization + ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k).factorization := by
      rw [hPmQ, Nat.factorization_mul hm0 hQ0]
    have hfacp : ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization p
        = m.factorization p + ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k).factorization p := by
      rw [hfac]; simp
    have h0 : m.factorization p = 0 := by omega
    have h1 : 1 ≤ m.factorization p := (Nat.Prime.dvd_iff_one_le_factorization hp hm0).mp hpm
    omega
  · intro hle
    have hdvd : ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ∣
        ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) := by
      rw [← Nat.factorization_le_iff_dvd hQ0 hP0, Finsupp.le_def]
      intro q
      by_cases hq : q.Prime
      · have hmq := master n q hn hq
        have hnn : 0 ≤ ∑ e ∈ Finset.Ico 1 n, T (n / q ^ e) := Nat.zero_le _
        omega
      · have h0q : ∀ x : ℕ, x ≠ 0 → x.factorization q = 0 := by
          intro x _
          simp [Nat.factorization, hq]
        have h1 := h0q _ hQ0
        have h2 := h0q _ hP0
        omega
    refine ⟨((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k)
      / ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k), ?_, ?_⟩
    · rw [Nat.cast_div hdvd (by exact_mod_cast hQ0)]
      simp only [OeisA129365.a, Nat.cast_prod, Nat.cast_pow]
    · have hfac : (((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k)
        / ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k)).factorization
          = ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization
            - ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k).factorization :=
        Nat.factorization_div hdvd
      have hfacp : (((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k)
        / ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k)).factorization p
          = ∑ e ∈ Finset.Ico 1 n, T (n / p ^ e) := by
        rw [hfac]
        show ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k).factorization p
            - ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k).factorization p = _
        rw [hmaster]
        omega
      have h1 : 1 ≤ ∑ e ∈ Finset.Ico 1 n, T (n / p ^ e) := by
        have h3p : 3 * p ≤ n := by omega
        have hnp : 3 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr h3p
        have hmem1 : (1 : ℕ) ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨le_refl _, by omega⟩
        have hT1 := one_le_T (n / p) hnp
        calc 1 = T (n / p ^ 1) := by rw [pow_one]; exact hT1
          _ ≤ ∑ e ∈ Finset.Ico 1 n, T (n / p ^ e) :=
              single_le_sum (fun _ _ => Nat.zero_le _) hmem1
      have hdiv0 : (((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k)
        / ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k)) ≠ 0 := by
        have hle' : ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k)
          ≤ ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero hP0) hdvd
        exact (Nat.div_pos hle' (Nat.pos_of_ne_zero hQ0)).ne'
      exact (Nat.Prime.dvd_iff_one_le_factorization hp hdiv0).mpr (by rw [hfacp]; exact h1)
