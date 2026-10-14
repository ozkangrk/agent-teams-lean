import FormalConjectures.OEIS.«129365»

open OeisA129365

theorem swarm_proof (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    (∃ m : ℕ, a n = m ∧ p ∣ m) ↔ p ≤ n / 3 := by
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
  have hdenpos : 0 < den := by
    refine Finset.prod_pos fun k _ => ?_
    exact Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hnumpos : 0 < num := by
    refine Finset.prod_pos fun j hj => Finset.prod_pos fun k _ => ?_
    exact Nat.gcd_pos_of_pos_left _ (hpos j hj)
  haveI hpF : Fact p.Prime := ⟨hp⟩
  have ha : a n = (num : ℚ) / (den : ℚ) := by
    simp only [a, ← Nat.cast_pow]
    simp only [← Nat.cast_prod]
    rw [← hnum_def, ← hden_def]
  have hval : ∀ q : ℕ, q.Prime →
      (∑ e ∈ Finset.Ico 1 (n+1), b (n / q ^ e)) + padicValNat q den = padicValNat q num := by
    intro q hq
    haveI hp' : Fact q.Prime := ⟨hq⟩
    have vprod : ∀ (s : Finset ℕ) (f : ℕ → ℕ), (∀ x ∈ s, f x ≠ 0) →
        padicValNat q (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat q (f x) := by
      intro s f hf
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha,
          padicValNat.mul (hf a (Finset.mem_insert_self a s))
          (Finset.prod_ne_zero_iff.mpr fun x hx => hf x (Finset.mem_insert_of_mem hx)), ih]
        intro x hx; exact hf x (Finset.mem_insert_of_mem hx)
    have vgcd : ∀ j k : ℕ, j ≠ 0 → k ≠ 0 →
        padicValNat q (Nat.gcd j k) = min (padicValNat q j) (padicValNat q k) := by
      intro j k hj hk
      have hgcdne : Nat.gcd j k ≠ 0 :=
        ne_of_gt (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hj))
      refine Nat.le_antisymm ?_ ?_
      · refine Nat.le_min.mpr ⟨?_, ?_⟩
        · have h : q ^ padicValNat q (Nat.gcd j k) ∣ j :=
            Nat.dvd_trans pow_padicValNat_dvd (Nat.gcd_dvd_left j k)
          exact (padicValNat_dvd_iff_le hj).mp h
        · have h : q ^ padicValNat q (Nat.gcd j k) ∣ k :=
            Nat.dvd_trans pow_padicValNat_dvd (Nat.gcd_dvd_right j k)
          exact (padicValNat_dvd_iff_le hk).mp h
      · have h1 : q ^ min (padicValNat q j) (padicValNat q k) ∣ j :=
          (padicValNat_dvd_iff_le hj).mpr (Nat.min_le_left _ _)
        have h2 : q ^ min (padicValNat q j) (padicValNat q k) ∣ k :=
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
        min (padicValNat q j) (padicValNat q k) =
          ∑ e ∈ Finset.Ico 1 (n+1), (if q ^ e ∣ j then (1:ℕ) else 0) * (if q ^ e ∣ k then (1:ℕ) else 0) := by
      intro j k hj hk
      have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
      have hpmj : q ^ min (padicValNat q j) (padicValNat q k) ∣ j :=
        (padicValNat_dvd_iff_le (hne' j hj)).mpr (Nat.min_le_left _ _)
      have hle : q ^ min (padicValNat q j) (padicValNat q k) ≤ j :=
        Nat.le_of_dvd (hpos j hj) hpmj
      have h2 : 2 ^ min (padicValNat q j) (padicValNat q k)
          ≤ q ^ min (padicValNat q j) (padicValNat q k) := Nat.pow_le_pow_left hq.two_le _
      have h5 : min (padicValNat q j) (padicValNat q k)
          < 2 ^ min (padicValNat q j) (padicValNat q k) := h2m _
      have hmn : min (padicValNat q j) (padicValNat q k) < n := by omega
      have hsub : Finset.Ico 1 (min (padicValNat q j) (padicValNat q k) + 1) ⊆ Finset.Ico 1 (n+1) :=
        Finset.Ico_subset_Ico (Nat.le_refl 1) (by omega)
      have hzero : ∀ e ∈ Finset.Ico 1 (n+1),
          e ∉ Finset.Ico 1 (min (padicValNat q j) (padicValNat q k) + 1) →
          (if q ^ e ∣ j then (1:ℕ) else 0) * (if q ^ e ∣ k then (1:ℕ) else 0) = 0 := by
        intro e he he'
        simp only [Finset.mem_Ico] at he he'
        have hem : min (padicValNat q j) (padicValNat q k) < e := by omega
        by_cases hje : q ^ e ∣ j
        · have hcon : ¬ q ^ e ∣ k := by
            intro hdvd
            have hle1 : e ≤ padicValNat q j := (padicValNat_dvd_iff_le (hne' j hj)).mp hje
            have hle2 : e ≤ padicValNat q k := (padicValNat_dvd_iff_le (hne' k hk)).mp hdvd
            exact absurd (Nat.le_min.mpr ⟨hle1, hle2⟩) (Nat.not_le.2 hem)
          rw [if_pos hje, if_neg hcon, mul_zero]
        · rw [if_neg hje, zero_mul]
      rw [← Finset.sum_subset hsub hzero]
      have hall : ∀ e ∈ Finset.Ico 1 (min (padicValNat q j) (padicValNat q k) + 1),
          (if q ^ e ∣ j then (1:ℕ) else 0) * (if q ^ e ∣ k then (1:ℕ) else 0) = 1 := by
        intro e he
        simp only [Finset.mem_Ico] at he
        have hem : e ≤ min (padicValNat q j) (padicValNat q k) := by omega
        have hjdvd : q ^ e ∣ j :=
          (padicValNat_dvd_iff_le (hne' j hj)).mpr (Nat.le_trans hem (Nat.min_le_left _ _))
        have hkdvd : q ^ e ∣ k :=
          (padicValNat_dvd_iff_le (hne' k hk)).mpr (Nat.le_trans hem (Nat.min_le_right _ _))
        rw [if_pos hjdvd, if_pos hkdvd]
      have hico : Finset.Ico 1 (min (padicValNat q j) (padicValNat q k) + 1)
          = Finset.Icc 1 (min (padicValNat q j) (padicValNat q k)) := by
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
    have vden : padicValNat q den = ∑ k ∈ Finset.Icc 1 n, k * ∑ e ∈ Finset.Ico 1 (n+1), n / (k * q ^ e) := by
      rw [hden_def, vprod _ _ (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _))]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [padicValNat.pow,
        padicValNat_factorial (show Nat.log q (n / k) < n + 1 by
          exact Nat.lt_succ_of_le (Nat.le_trans (Nat.log_le_self q (n / k))
            (Nat.div_le_self n k)))]
      simp only [Nat.div_div_eq_div_mul]
    have vden' : padicValNat q den = ∑ e ∈ Finset.Ico 1 (n+1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * q ^ e)) := by
      rw [vden]
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    have vnum : padicValNat q num = ∑ e ∈ Finset.Ico 1 (n+1), (n / q ^ e) * (n / q ^ e) := by
      have hexp : padicValNat q num
          = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, padicValNat q (Nat.gcd j k) := by
        rw [hnum_def, vprod _ _ (fun j hj =>
          Finset.prod_ne_zero_iff.mpr fun k _ => ne_of_gt (Nat.gcd_pos_of_pos_left _ (hpos j hj)))]
        refine Finset.sum_congr rfl fun j hj =>
          vprod _ _ (fun k hk => ne_of_gt (Nat.gcd_pos_of_pos_left _ (hpos j hj)))
      rw [hexp]
      have step1 : ∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n,
          padicValNat q (Nat.gcd j k) =
            ∑ e ∈ Finset.Ico 1 (n+1), (if q ^ e ∣ j then (1:ℕ) else 0) * (if q ^ e ∣ k then (1:ℕ) else 0) := by
        intro j hj k hk
        rw [vgcd j k (hne' j hj) (hne' k hk), vmin j k hj hk]
      rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => step1 j hj k hk)),
        keyswap (fun j k e => (if q ^ e ∣ j then (1:ℕ) else 0) * (if q ^ e ∣ k then (1:ℕ) else 0))]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [← Finset.sum_mul_sum, indsum (q ^ e) (pow_pos hq.pos e)]
    have perE : ∀ e ∈ Finset.Ico 1 (n+1),
        b (n / q ^ e) + (∑ k ∈ Finset.Icc 1 n, k * (n / (k * q ^ e))) = (n / q ^ e) * (n / q ^ e) := by
      intro e he
      obtain ⟨q1, hqdef⟩ : ∃ q1, q ^ e = q1 := ⟨_, rfl⟩
      have hq1 : 0 < q1 := by rw [← hqdef]; exact pow_pos hq.pos e
      obtain ⟨N, hNdef⟩ : ∃ N, n / q1 = N := ⟨_, rfl⟩
      have hNn : N ≤ n := by rw [← hNdef]; exact Nat.div_le_self n q1
      have hunion : Finset.Icc 1 n = Finset.Icc 1 N ∪ Finset.Icc (N+1) n := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N+1) n) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        simp only [Finset.mem_Icc] at h1 h2
        omega
      have hnq : n < q1 * N + q1 := by
        have h1 := Nat.div_add_mod n q1
        rw [hNdef] at h1
        have h2 : n % q1 < q1 := Nat.mod_lt n hq1
        nlinarith [h1, h2]
      have h0 : ∀ k ∈ Finset.Icc (N+1) n, k * (n / (k * q1)) = 0 := by
        intro k hk
        simp only [Finset.mem_Icc] at hk
        have hkq : n < k * q1 := by
          have hA : (N + 1) * q1 ≤ k * q1 := Nat.mul_le_mul_right q1 hk.1
          have hB : q1 * N + q1 = (N + 1) * q1 := by ring
          nlinarith [hnq, hA, hB]
        rw [Nat.div_eq_of_lt hkq, mul_zero]
      have hsplit : ∑ k ∈ Finset.Icc 1 n, k * (n / (k * q1))
          = ∑ k ∈ Finset.Icc 1 N, k * (N / k) := by
        rw [hunion, Finset.sum_union hdisj, Finset.sum_eq_zero h0, add_zero]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hke : n / (k * q1) = N / k := by
          rw [show n / (k * q1) = n / (q1 * k) from by rw [Nat.mul_comm],
            ← Nat.div_div_eq_div_mul, hNdef]
        rw [hke]
      have hbN : b N = ∑ k ∈ Finset.Icc 1 N, N % k := rfl
      calc b (n / q ^ e) + (∑ k ∈ Finset.Icc 1 n, k * (n / (k * q ^ e)))
          = b (n / q1) + (∑ k ∈ Finset.Icc 1 n, k * (n / (k * q1))) := by rw [hqdef]
        _ = b N + (∑ k ∈ Finset.Icc 1 N, k * (N / k)) := by rw [hsplit, hNdef]
        _ = (∑ k ∈ Finset.Icc 1 N, N % k) + (∑ k ∈ Finset.Icc 1 N, k * (N / k)) := by rw [hbN]
        _ = ∑ k ∈ Finset.Icc 1 N, (N % k + k * (N / k)) := Finset.sum_add_distrib.symm
        _ = ∑ k ∈ Finset.Icc 1 N, N := Finset.sum_congr rfl
          fun k hk => by rw [Nat.add_comm]; exact Nat.div_add_mod N k
        _ = N * N := by rw [Finset.sum_const, smul_eq_mul, cardEq]
        _ = (n / q ^ e) * (n / q ^ e) := by rw [hqdef, hNdef]
    have hsum : ((∑ e ∈ Finset.Ico 1 (n+1), b (n / q ^ e))
        + ∑ e ∈ Finset.Ico 1 (n+1), ∑ k ∈ Finset.Icc 1 n, k * (n / (k * q ^ e)))
        = ∑ e ∈ Finset.Ico 1 (n+1), (n / q ^ e) * (n / q ^ e) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl perE
    omega
  have hbsum : ∀ N : ℕ, b N = ∑ k ∈ Finset.Icc 1 N, N % k := fun N => rfl
  have bsmall : ∀ N : ℕ, N ≤ 2 → b N = 0 := by
    intro N hN
    rcases N with _ | _ | _ | N'
    · decide
    · decide
    · decide
    · omega
  have bge3 : ∀ N : ℕ, 3 ≤ N → 1 ≤ b N := by
    intro N hN
    have hmem : (N - 1) ∈ Finset.Icc 1 N := by simp only [Finset.mem_Icc]; omega
    have hmod : N % (N - 1) = 1 := by
      have hlt : 1 < N - 1 := by omega
      conv_lhs => rw [show N = N - 1 + 1 from by omega]
      simp only [Nat.add_sub_cancel]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
    calc 1 = N % (N - 1) := hmod.symm
      _ ≤ ∑ k ∈ Finset.Icc 1 N, N % k :=
          Finset.single_le_sum (f := fun k => N % k) (fun k _ => Nat.zero_le _) hmem
      _ = b N := (hbsum N).symm
  obtain ⟨BB, hBB⟩ : ∃ BB, BB = ∑ e ∈ Finset.Ico 1 (n+1), b (n / p ^ e) := ⟨_, rfl⟩
  have hvdnen : (den : ℚ) ≠ 0 := by exact_mod_cast hden
  have hvcnum : (num : ℚ) ≠ 0 := by exact_mod_cast hnum
  have master : padicValRat p (a n) = ((BB : ℤ)) := by
    rw [ha, padicValRat.div hvcnum hvdnen, ← padicValRat_of_nat, ← padicValRat_of_nat]
    have hv := hval p hp
    omega
  constructor
  · rintro ⟨m, hmeq, hmdvd⟩
    by_contra hcon
    have hap : 0 < a n := by
      rw [ha]
      exact div_pos (Nat.cast_pos.mpr hnumpos) (Nat.cast_pos.mpr hdenpos)
    have hmne : m ≠ 0 := by
      intro h0
      rw [h0] at hmeq
      rw [hmeq] at hap
      exact absurd hap (lt_irrefl 0)
    have hvm1 : 1 ≤ padicValNat p m := by
      have hpp : p ^ 1 ∣ m := by rw [pow_one]; exact hmdvd
      exact (padicValNat_dvd_iff_le hmne).mp hpp
    have hv1 : padicValRat p (a n) = ((padicValNat p m : ℤ)) := by
      rw [hmeq, padicValRat_of_nat]
    have hlt3 : n / 3 < p := Nat.lt_of_not_ge hcon
    have hnlt : n < p * 3 := (Nat.div_lt_iff_lt_mul (show (0:ℕ) < 3 by norm_num)).mp hlt3
    have hnp2 : n / p ≤ 2 := by
      by_contra hc
      have h3le : 3 ≤ n / p := Nat.succ_le_of_lt (Nat.lt_of_not_le hc)
      have h3p : 3 * p ≤ n := (Nat.le_div_iff_mul_le hp.pos).mp h3le
      omega
    have hB0 : BB = 0 := by
      rw [hBB]
      apply Finset.sum_eq_zero
      intro e he
      apply bsmall
      rcases (Finset.mem_Ico.mp he) with ⟨he1, _⟩
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      have hpe : p ≤ p ^ (e' + 1) := by
        rw [pow_succ']
        calc p = p * 1 := (mul_one p).symm
          _ ≤ p * p ^ e' := Nat.mul_le_mul_left p
            (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (pow_pos hp.pos e')))
      have hd1 : n / p ^ (e' + 1) ≤ n / p := Nat.div_le_div (le_refl n) hpe hp.ne_zero
      exact Nat.le_trans hd1 hnp2
    rw [master] at hv1
    omega
  · intro hle
    have h3 : p * 3 ≤ n := (Nat.le_div_iff_mul_le (show (0:ℕ) < 3 by norm_num)).mp hle
    have hnp : 3 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr (show 3 * p ≤ n by omega)
    have hB1 : 1 ≤ BB := by
      rw [hBB]
      have hmem : (1:ℕ) ∈ Finset.Ico 1 (n+1) := by simp only [Finset.mem_Ico]; omega
      exact Nat.le_trans (bge3 (n / p ^ 1) (by rw [pow_one]; exact hnp))
        (Finset.single_le_sum (f := fun e => b (n / p ^ e)) (fun x _ => Nat.zero_le _) hmem)
    have hdvd : den ∣ num := by
      rw [← Nat.factorization_le_iff_dvd hden hnum]
      intro qq
      by_cases hqq : qq.Prime
      · rw [Nat.factorization_def _ hqq, Nat.factorization_def _ hqq]
        have hv := hval qq hqq
        omega
      · simp only [Nat.factorization_eq_zero_of_not_prime _ hqq]
        exact Nat.zero_le _
    have hqne0 : num / den ≠ 0 := by
      intro h0
      have hdm : den * (num / den) = num := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdvd
      rw [h0, mul_zero] at hdm
      exact hnum hdm.symm
    have hmdvd : p ∣ num / den := by
      have hdm : den * (num / den) = num := by rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdvd
      have hv := padicValNat.mul (p := p) hden hqne0
      rw [hdm] at hv
      have hvv := hval p hp
      have h1vm : 1 ≤ padicValNat p (num / den) := by omega
      have hp1v : p ^ 1 ∣ p ^ padicValNat p (num / den) :=
        pow_dvd_pow_of_dvd_of_le (dvd_refl p) h1vm
      have hpv : p ^ padicValNat p (num / den) ∣ num / den :=
        (padicValNat_dvd_iff_le hqne0).mpr (Nat.le_refl _)
      have hfin : p ^ 1 ∣ num / den := Nat.dvd_trans hp1v hpv
      rw [pow_one] at hfin
      exact hfin
    refine ⟨num / den, ?_, hmdvd⟩
    rw [ha]
    exact (Nat.cast_div hdvd (by exact_mod_cast hden)).symm
