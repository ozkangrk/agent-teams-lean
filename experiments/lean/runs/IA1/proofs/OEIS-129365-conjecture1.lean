
import FormalConjectures.OEIS.«129365»

open OeisA129365

theorem swarm_proof : ∀ (n : ℕ), 0 < n →
    ((Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k) ∣
      ((Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k) := by
  intro n hn
  classical
  set den : ℕ := (Finset.Icc 1 n).prod fun k => (n / k).factorial ^ k with hden_def
  set num : ℕ := (Finset.Icc 1 n).prod fun j => (Finset.Icc 1 n).prod fun k => Nat.gcd j k with hnum_def
  have hpos : ∀ j ∈ Finset.Icc 1 n, 0 < j := by
    intro j hj
    have := Finset.mem_Icc.mp hj
    omega
  have hne' : ∀ j ∈ Finset.Icc 1 n, j ≠ 0 := by
    intro j hj
    exact ne_of_gt (hpos j hj)
  have hden : den ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    exact pow_ne_zero _ (Nat.factorial_ne_zero _)
  have hnum : num ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    exact ne_of_gt (Nat.gcd_pos_of_pos_left _ (hpos j hj))
  rw [← Nat.factorization_le_iff_dvd hden hnum]
  intro p
  by_cases hp : p.Prime
  · haveI hp' : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    have vprod : ∀ (s : Finset ℕ) (f : ℕ → ℕ), (∀ x ∈ s, f x ≠ 0) →
        padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
      intro s f hf
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha,
          padicValNat.mul (hf a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.mpr fun x hx => hf x (Finset.mem_insert_of_mem hx)), ih]
        intro x hx; exact hf x (Finset.mem_insert_of_mem hx)
    have vgcd : ∀ j k : ℕ, j ≠ 0 → k ≠ 0 →
        padicValNat p (Nat.gcd j k) = min (padicValNat p j) (padicValNat p k) := by
      intro j k hj hk
      have hgcdne : Nat.gcd j k ≠ 0 :=
        ne_of_gt (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hj))
      refine Nat.le_antisymm ?_ ?_
      · refine Nat.le_min.mpr ⟨?_, ?_⟩
        · have h : p ^ padicValNat p (Nat.gcd j k) ∣ j :=
            Nat.dvd_trans pow_padicValNat_dvd (Nat.gcd_dvd_left j k)
          exact (padicValNat_dvd_iff_le hj).mp h
        · have h : p ^ padicValNat p (Nat.gcd j k) ∣ k :=
            Nat.dvd_trans pow_padicValNat_dvd (Nat.gcd_dvd_right j k)
          exact (padicValNat_dvd_iff_le hk).mp h
      · have h1 : p ^ min (padicValNat p j) (padicValNat p k) ∣ j :=
          (padicValNat_dvd_iff_le hj).mpr (Nat.min_le_left _ _)
        have h2 : p ^ min (padicValNat p j) (padicValNat p k) ∣ k :=
          (padicValNat_dvd_iff_le hk).mpr (Nat.min_le_right _ _)
        exact (padicValNat_dvd_iff_le hgcdne).mp (Nat.dvd_gcd h1 h2)
    have h2m : ∀ d : ℕ, d < 2 ^ d := by
      intro d
      induction d with
      | zero => norm_num
      | succ d ih =>
        have hp1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
        have hexp : 2 ^ (d+1) = 2 ^ d + 2 ^ d := by ring
        omega
    have cardEq : ∀ m : ℕ, (Finset.Icc 1 m).card = m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hext : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnm : m + 1 ∉ Finset.Icc 1 m := by
          intro hc
          simp only [Finset.mem_Icc] at hc
          omega
        rw [hext, Finset.card_insert_of_notMem hnm, ih]
    have vmin : ∀ j k : ℕ, j ∈ Finset.Icc 1 n → k ∈ Finset.Icc 1 n →
        min (padicValNat p j) (padicValNat p k) =
          ∑ e ∈ Finset.Ico 1 (n+1), (if p ^ e ∣ j then (1:ℕ) else 0) * (if p ^ e ∣ k then (1:ℕ) else 0) := by
      intro j k hj hk
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      have hpmj : p ^ min (padicValNat p j) (padicValNat p k) ∣ j :=
        (padicValNat_dvd_iff_le (hne' j hj)).mpr (Nat.min_le_left _ _)
      have hle : p ^ min (padicValNat p j) (padicValNat p k) ≤ j :=
        Nat.le_of_dvd (hpos j hj) hpmj
      have h2 : 2 ^ min (padicValNat p j) (padicValNat p k)
          ≤ p ^ min (padicValNat p j) (padicValNat p k) := Nat.pow_le_pow_left hp.two_le _
      have h5 : min (padicValNat p j) (padicValNat p k)
          < 2 ^ min (padicValNat p j) (padicValNat p k) := h2m _
      have hmn : min (padicValNat p j) (padicValNat p k) < n := by omega
      have hsub : Finset.Ico 1 (min (padicValNat p j) (padicValNat p k) + 1) ⊆ Finset.Ico 1 (n+1) :=
        Finset.Ico_subset_Ico (Nat.le_refl 1) (by omega)
      have hzero : ∀ e ∈ Finset.Ico 1 (n+1),
          e ∉ Finset.Ico 1 (min (padicValNat p j) (padicValNat p k) + 1) →
          (if p ^ e ∣ j then (1:ℕ) else 0) * (if p ^ e ∣ k then (1:ℕ) else 0) = 0 := by
        intro e he he'
        simp only [Finset.mem_Ico] at he he'
        have hem : min (padicValNat p j) (padicValNat p k) < e := by omega
        by_cases hje : p ^ e ∣ j
        · have hcon : ¬ p ^ e ∣ k := by
            intro hdvd
            have hle1 : e ≤ padicValNat p j := (padicValNat_dvd_iff_le (hne' j hj)).mp hje
            have hle2 : e ≤ padicValNat p k := (padicValNat_dvd_iff_le (hne' k hk)).mp hdvd
            exact absurd (Nat.le_min.mpr ⟨hle1, hle2⟩) (Nat.not_le.2 hem)
          rw [if_pos hje, if_neg hcon, mul_zero]
        · rw [if_neg hje, zero_mul]
      rw [← Finset.sum_subset hsub hzero]
      have hall : ∀ e ∈ Finset.Ico 1 (min (padicValNat p j) (padicValNat p k) + 1),
          (if p ^ e ∣ j then (1:ℕ) else 0) * (if p ^ e ∣ k then (1:ℕ) else 0) = 1 := by
        intro e he
        simp only [Finset.mem_Ico] at he
        have hem : e ≤ min (padicValNat p j) (padicValNat p k) := by omega
        have hjdvd : p ^ e ∣ j :=
          (padicValNat_dvd_iff_le (hne' j hj)).mpr (Nat.le_trans hem (Nat.min_le_left _ _))
        have hkdvd : p ^ e ∣ k :=
          (padicValNat_dvd_iff_le (hne' k hk)).mpr (Nat.le_trans hem (Nat.min_le_right _ _))
        rw [if_pos hjdvd, if_pos hkdvd]
      have hico : Finset.Ico 1 (min (padicValNat p j) (padicValNat p k) + 1)
          = Finset.Icc 1 (min (padicValNat p j) (padicValNat p k)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [Finset.sum_congr rfl hall]
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hico, cardEq]
    have cardIcc : ∀ q : ℕ, 0 < q → ((Finset.Icc 1 n).filter (fun j => q ∣ j)).card = n / q := by
      intro q hq
      have hset : (Finset.Icc 1 n).filter (fun j => q ∣ j)
          = (Finset.range (n+1)).filter (fun k => k ≠ 0 ∧ q ∣ k) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨by omega, by omega, h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨by omega, by omega⟩, h3⟩
      rw [hset]
      exact Nat.card_multiples' n q
    have sumitecard : ∀ (s : Finset ℕ) (q : ℕ),
        (∑ j ∈ s, (if q ∣ j then (1:ℕ) else 0)) = (s.filter (fun j => q ∣ j)).card := by
      intro s q
      have h1 : ∑ j ∈ s, (if q ∣ j then (1:ℕ) else 0) = ∑ j ∈ s.filter (fun j => q ∣ j), 1 :=
        (Finset.sum_filter (fun j => q ∣ j) (fun _ => (1:ℕ))).symm
      rw [h1]
      simp
    have indsum : ∀ q : ℕ, 0 < q →
        ∑ j ∈ Finset.Icc 1 n, (if q ∣ j then (1:ℕ) else 0) = n / q := by
      intro q hq
      rw [sumitecard, cardIcc q hq]
    have keyswap : ∀ f : ℕ → ℕ → ℕ → ℕ,
        (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ∑ e ∈ Finset.Ico 1 (n+1), f j k e)
          = ∑ e ∈ Finset.Ico 1 (n+1), ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f j k e := by
      intro f
      calc (∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ∑ e ∈ Finset.Ico 1 (n+1), f j k e)
          = ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, ∑ e ∈ Finset.Ico 1 (n+1), f j k e := Finset.sum_comm
        _ = ∑ k ∈ Finset.Icc 1 n, ∑ e ∈ Finset.Ico 1 (n+1), ∑ j ∈ Finset.Icc 1 n, f j k e :=
            Finset.sum_congr rfl fun k _ => Finset.sum_comm
        _ = ∑ e ∈ Finset.Ico 1 (n+1), ∑ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n, f j k e := Finset.sum_comm
        _ = ∑ e ∈ Finset.Ico 1 (n+1), ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f j k e :=
            Finset.sum_congr rfl fun e _ => Finset.sum_comm
    have vden : padicValNat p den = ∑ k ∈ Finset.Icc 1 n, k * ∑ e ∈ Finset.Ico 1 (n+1), n / (k * p ^ e) := by
      rw [hden_def, vprod _ _ (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _))]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [padicValNat.pow,
        padicValNat_factorial (show Nat.log p (n / k) < n + 1 by
          exact Nat.lt_succ_of_le (Nat.le_trans (Nat.log_le_self p (n / k))
            (Nat.div_le_self n k)))]
      simp only [Nat.div_div_eq_div_mul]
    have vden' : padicValNat p den = ∑ e ∈ Finset.Ico 1 (n+1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * p ^ e)) := by
      rw [vden]
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    have vnum : padicValNat p num = ∑ e ∈ Finset.Ico 1 (n+1), (n / p ^ e) * (n / p ^ e) := by
      have hexp : padicValNat p num
          = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, padicValNat p (Nat.gcd j k) := by
        rw [hnum_def, vprod _ _ (fun j hj =>
          Finset.prod_ne_zero_iff.mpr fun k _ => ne_of_gt (Nat.gcd_pos_of_pos_left _ (hpos j hj)))]
        refine Finset.sum_congr rfl fun j hj =>
          vprod _ _ (fun k hk => ne_of_gt (Nat.gcd_pos_of_pos_left _ (hpos j hj)))
      rw [hexp]
      have step1 : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
          padicValNat p (Nat.gcd j k) =
            ∑ e ∈ Finset.Ico 1 (n+1), (if p ^ e ∣ j then (1:ℕ) else 0) * (if p ^ e ∣ k then (1:ℕ) else 0) := by
        intro j hj k hk
        rw [vgcd j k (hne' j hj) (hne' k hk), vmin j k hj hk]
      rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => step1 j hj k hk)),
        keyswap (fun j k e => (if p ^ e ∣ j then (1:ℕ) else 0) * (if p ^ e ∣ k then (1:ℕ) else 0))]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_mul_sum, indsum (p ^ e) (pow_pos hp.pos e)]
    have pere : ∀ e ∈ Finset.Ico 1 (n+1),
        ∑ k ∈ Finset.Icc 1 n, k * (n / (k * p ^ e)) ≤ (n / p ^ e) * (n / p ^ e) := by
      intro e he
      obtain ⟨q, hqdef⟩ : ∃ q, p ^ e = q := ⟨_, rfl⟩
      have hq : 0 < q := by rw [← hqdef]; exact pow_pos hp.pos e
      obtain ⟨N, hNdef⟩ : ∃ N, n / q = N := ⟨_, rfl⟩
      have hNn : N ≤ n := by rw [← hNdef]; exact Nat.div_le_self n q
      have hunion : Finset.Icc 1 n = Finset.Icc 1 N ∪ Finset.Icc (N+1) n := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N+1) n) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        simp only [Finset.mem_Icc] at h1 h2
        omega
      have hnq : n < q * N + q := by
        have h1 := Nat.div_add_mod n q
        rw [hNdef] at h1
        have h2 : n % q < q := Nat.mod_lt n hq
        nlinarith [h1, h2]
      rw [hunion, Finset.sum_union hdisj, hqdef]
      have h0 : ∀ k ∈ Finset.Icc (N+1) n, k * (n / (k * q)) = 0 := by
        intro k hk
        simp only [Finset.mem_Icc] at hk
        have hkq : n < k * q := by
          have hA : (N + 1) * q ≤ k * q := Nat.mul_le_mul_right q hk.1
          have hB : q * N + q = (N + 1) * q := by ring
          nlinarith [hnq, hA, hB]
        rw [Nat.div_eq_of_lt hkq, mul_zero]
      have htail : ∑ k ∈ Finset.Icc (N+1) n, k * (n / (k * q)) = 0 :=
        Finset.sum_eq_zero fun k hk => h0 k hk
      rw [htail, add_zero]
      have termle : ∀ k : ℕ, k * (n / (k * q)) ≤ N := by
        intro k
        have h1 : (k * (n / (k * q))) * q ≤ n := by
          have hdm := Nat.div_mul_le_self n (k * q)
          calc (k * (n / (k * q))) * q = (n / (k * q)) * (k * q) := by ring
            _ ≤ n := hdm
        have hres : k * (n / (k * q)) ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr h1
        rw [hNdef] at hres
        exact hres
      calc ∑ k ∈ Finset.Icc 1 N, k * (n / (k * q)) ≤ ∑ k ∈ Finset.Icc 1 N, N :=
            Finset.sum_le_sum fun k _ => termle k
        _ = (Finset.Icc 1 N).card * N := by rw [Finset.sum_const, smul_eq_mul]
        _ = N * N := by rw [cardEq]
        _ = (n / q) * (n / q) := by rw [hNdef]
    calc padicValNat p den = ∑ e ∈ Finset.Ico 1 (n+1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * p ^ e)) := vden'
      _ ≤ ∑ e ∈ Finset.Ico 1 (n+1), (n / p ^ e) * (n / p ^ e) := Finset.sum_le_sum pere
      _ = padicValNat p num := vnum.symm
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]
    apply Nat.zero_le
