import FormalConjectures.OEIS.«237271»

open OeisA237271
open Nat Finset List

theorem swarm_proof (k : ℕ) (hk : IsCarmichael k) : 3 ≤ a k := by
  obtain ⟨_, hnp, hk1⟩ := hk 1 (by norm_num) (coprime_one_right k)
  have hk0 : 0 < k := by omega
  have hkodd : ¬ 2 ∣ k := by
    intro h2
    have h4 : 4 ≤ k := by
      rcases Nat.lt_or_ge k 4 with h | h
      · rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
        · exact absurd Nat.prime_two hnp
        · exact absurd Nat.prime_three hnp
      · omega
    have hcop : k.Coprime (k - 1) := by
      rw [Nat.coprime_self_sub_right (by omega)]
      exact coprime_one_right k
    obtain ⟨hpr, _, _⟩ := hk (k - 1) (by omega) hcop
    have hge : 1 ≤ (k - 1) ^ (k - 1) := by
      have hmono := Nat.pow_le_pow_right (show 0 < k - 1 by omega) (show 1 ≤ k - 1 by omega)
      have hp1 : (k - 1) ^ 1 = k - 1 := pow_one _
      omega
    have hX' : (k:ℤ) ∣ ((k:ℤ) - 1) ^ (k - 1) - 1 := by
      have h1' : (k:ℤ) ∣ (((k - 1) ^ (k - 1) - 1 : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.2 hpr
      have h2' : (((k - 1) ^ (k - 1) - 1 : ℕ) : ℤ) = ((k:ℤ) - 1) ^ (k - 1) - 1 := by
        rw [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_sub (by omega), Nat.cast_one]
      rw [h2'] at h1'
      exact h1'
    have hone : ((k:ℤ) - 1) ^ (k - 1) ≡ 1 [ZMOD k] := by
      refine Int.modEq_of_dvd ?_
      obtain ⟨c, hc⟩ := hX'
      refine ⟨-c, ?_⟩
      rw [show (1:ℤ) - ((k:ℤ) - 1) ^ (k - 1) = -(((k:ℤ) - 1) ^ (k - 1) - 1) from by ring, hc]
      ring
    have hm : ((k:ℤ) - 1) ≡ (-1:ℤ) [ZMOD k] :=
      Int.modEq_of_dvd ⟨-1, by ring⟩
    have hp2 := hm.pow (k - 1)
    have hneg : ((-1:ℤ)) ^ (k - 1) = -1 := by
      obtain ⟨w, hw⟩ := h2
      have hw2 : k - 1 = 2 * (w - 1) + 1 := by omega
      rw [hw2, pow_succ, pow_mul, neg_one_pow_two, one_pow]
      norm_num
    rw [hneg] at hp2
    obtain ⟨c, hc⟩ := Int.ModEq.dvd (hp2.symm.trans hone)
    by_cases hc0 : 0 ≤ c
    · rcases eq_or_lt_of_le hc0 with rfl | h1c
      · omega
      · have h2c : (k:ℤ) * 1 ≤ (k:ℤ) * c :=
          Int.mul_le_mul_of_nonneg_left h1c (by omega : (0:ℤ) ≤ (k:ℤ))
        linarith [hc]
    · have hnn := Int.mul_nonneg (by omega : (0:ℤ) ≤ (k:ℤ)) (by omega : (0:ℤ) ≤ -c)
      have hring : (k:ℤ) * (-c) = -((k:ℤ) * c) := by ring
      linarith [hc]
  -- divisor list
  rw [OeisA237271.a]
  set L : List ℕ := k.divisors.sort (· ≤ ·) with hL
  have hmemL : ∀ d, d ∈ L ↔ d ∈ k.divisors := by
    intro d; rw [hL]; exact Finset.mem_sort ..
  have hdvd : ∀ d ∈ L, d ∣ k ∧ 0 < d := by
    intro d hd
    obtain ⟨hd1, hk1'⟩ := Nat.mem_divisors.1 ((hmemL d).1 hd)
    refine ⟨hd1, ?_⟩
    by_contra hcon
    have hd0 : d = 0 := by omega
    rw [hd0] at hd1
    obtain ⟨w, hw⟩ := hd1
    omega
  have hLodd : ∀ d ∈ L, Odd d := by
    intro d hd
    rcases Nat.even_or_odd d with he | ho
    · exact absurd (dvd_trans (by obtain ⟨w, rfl⟩ := he; exact ⟨w, by omega⟩) (hdvd d hd).1) hkodd
    · exact ho
  have hpwL : List.Pairwise (· ≤ ·) L := by rw [hL]; exact Finset.pairwise_sort _ _
  have hndL : L.Nodup := by rw [hL]; exact Finset.sort_nodup _ _
  have hle : ∀ d ∈ L, d ≤ k := fun d hd => Nat.le_of_dvd hk0 (hdvd d hd).1
  have h1L : (1:ℕ) ∈ L := (hmemL 1).2 (Nat.mem_divisors.2 ⟨one_dvd k, by omega⟩)
  have hkL : k ∈ L := (hmemL k).2 (Nat.mem_divisors.2 ⟨dvd_rfl, by omega⟩)
  obtain ⟨m, hmdvd, hmne1, hmnek⟩ := Nat.exists_dvd_of_not_prime (by omega) hnp
  have hmL : m ∈ L := (hmemL m).2 (Nat.mem_divisors.2 ⟨hmdvd, by omega⟩)
  have hlen3 : 3 ≤ L.length := by
    have hsub : (insert k (insert m (insert 1 (∅ : Finset ℕ)))) ⊆ k.divisors := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Nat.mem_divisors.2 ⟨dvd_rfl, by omega⟩
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Nat.mem_divisors.2 ⟨hmdvd, by omega⟩
        · rcases Finset.mem_insert.1 hx with rfl | hx
          · exact Nat.mem_divisors.2 ⟨one_dvd k, by omega⟩
          · exact absurd hx (by simp)
    have hc3 : (insert k (insert m (insert 1 (∅ : Finset ℕ)))).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            intro h
            rcases Finset.mem_insert.1 h with h' | h'
            · exact hmnek h'.symm
            · rcases Finset.mem_insert.1 h' with h'' | h''
              · omega
              · exact absurd h'' (by simp)),
          Finset.card_insert_of_notMem (by
            intro h
            rcases Finset.mem_insert.1 h with h' | h'
            · exact hmne1 h'
            · exact absurd h' (by simp)),
          Finset.card_insert_of_notMem (by simp)]
      simp
    have hcc := Finset.card_le_card hsub
    rw [hc3] at hcc
    rw [hL, Finset.length_sort]
    omega
  -- head = 1, L = 1 :: d2 :: rest
  obtain ⟨hd, t, hLc⟩ : ∃ hd t, L = hd :: t := by
    rcases L with _ | ⟨hd, t⟩
    · simp at hlen3
    · exact ⟨hd, t, rfl⟩
  have h1Lc : 1 ∈ hd :: t := by rw [← hLc]; exact h1L
  have hpwLc : List.Pairwise (· ≤ ·) (hd :: t) := by rw [← hLc]; exact hpwL
  have hhd1 : hd = 1 := by
    rcases List.mem_cons.1 h1Lc with rfl | h1int
    · rfl
    · have hle1 : hd ≤ 1 := rel_of_pairwise_cons hpwLc h1int
      have hdL : hd ∈ L := by rw [hLc]; exact List.mem_cons_self
      have := (hdvd hd hdL).2
      omega
  rw [hhd1] at hLc
  obtain ⟨d2, rest, htc⟩ : ∃ d2 rest, t = d2 :: rest := by
    rcases t with _ | ⟨d2, rest⟩
    · rw [hLc] at hlen3; simp at hlen3
    · exact ⟨d2, rest, rfl⟩
  rw [htc] at hLc
  have hd2L : d2 ∈ L := by rw [hLc]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hd2dvd := (hdvd d2 hd2L)
  have hd2odd := hLodd d2 hd2L
  have hd2ge2 : 2 ≤ d2 := by
    have h12 : d2 ≠ 1 := by
      intro hcon
      have hndLc : List.Nodup (1 :: d2 :: rest) := by rw [← hLc]; exact hndL
      have hmem1 := (List.nodup_cons.1 hndLc).1
      exact hmem1 (by rw [hcon]; exact List.mem_cons_self)
    have := hd2dvd.2
    omega
  -- index lemmas
  have idxle : ∀ (l : List ℕ), List.Pairwise (· ≤ ·) l → ∀ (i j : ℕ) (hi : i < l.length)
      (hj : j < l.length), i ≤ j → l[i] ≤ l[j] := by
    intro l hp
    induction l with
    | nil => intro i j hi hj _; simp at hi
    | cons a t ih =>
      intro i j hi hj hij
      match i, j with
      | 0, 0 => exact le_rfl
      | i+1, 0 => omega
      | 0, j+1 =>
        have hj' : j < t.length := by simpa using hj
        have hrel := List.rel_of_pairwise_cons hp (List.getElem_mem hj')
        have h1 : (a :: t)[0]'(by simp) = a := List.getElem_cons_zero a t (by simp)
        have h2 : (a :: t)[j+1]'hj = t[j]'hj' := List.getElem_cons_succ a t j hj
        rw [h1, h2]
        exact hrel
      | i+1, j+1 =>
        have hi' : i < t.length := by simpa using hi
        have hj' : j < t.length := by simpa using hj
        rw [List.getElem_cons_succ a t i hi, List.getElem_cons_succ a t j hj]
        exact ih (List.Pairwise.of_cons hp) i j hi' hj' (by omega)
  have posne : ∀ (l : List ℕ), l.Nodup → ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      i ≠ j → l[i] ≠ l[j] := by
    intro l hnd
    induction l with
    | nil => intro i j hi hj _; simp at hi
    | cons a t ih =>
      intro i j hi hj hij
      match i, j with
      | 0, 0 => exact absurd rfl hij
      | i+1, 0 =>
        intro hcon
        have hi' : i < t.length := by simpa using hi
        have hmem : t[i]'hi' ∈ t := List.getElem_mem hi'
        rw [List.getElem_cons_succ a t i hi, List.getElem_cons_zero a t (by simp)] at hcon
        exact (List.nodup_cons.1 hnd).1 (hcon ▸ hmem)
      | 0, j+1 =>
        have hj' : j < t.length := by simpa using hj
        have hmem : t[j]'hj' ∈ t := List.getElem_mem hj'
        intro hcon
        have h0 : (a :: t)[0]'(by simp) = a := List.getElem_cons_zero a t (by simp)
        have h1 : (a :: t)[j+1]'hj = t[j]'hj' := List.getElem_cons_succ a t j hj
        rw [h0, h1] at hcon
        exact (List.nodup_cons.1 hnd).1 (hcon ▸ hmem)
      | i+1, j+1 =>
        have hi' : i < t.length := by simpa using hi
        have hj' : j < t.length := by simpa using hj
        rw [List.getElem_cons_succ a t i hi, List.getElem_cons_succ a t j hj]
        exact ih (List.Nodup.of_cons hnd) i j hi' hj' (by omega)
  -- last element is k
  have hlastlen : L.length - 1 < L.length := by omega
  have hn2len : L.length - 2 < L.length := by omega
  have hlast : L[L.length - 1]'hlastlen = k := by
    obtain ⟨i, hi, hik⟩ := List.mem_iff_getElem.1 hkL
    have hy := List.getElem_mem hlastlen
    have hyk : L[L.length - 1]'hlastlen ≤ k := hle _ hy
    have hk1' : L[i] ≤ L[L.length - 1]'hlastlen :=
      idxle L hpwL i (L.length - 1) hi hlastlen (by omega)
    rw [hik] at hk1'
    omega
  -- the second-to-last element d'
  have hn2t : L.length - 2 < L.tail.length := by simp; omega
  obtain ⟨hd'dvd, hd'pos⟩ := hdvd _ (List.getElem_mem hn2len)
  have hd'odd := hLodd _ (List.getElem_mem hn2len)
  have hd'nek : L[L.length - 2]'hn2len ≠ k := by
    intro hcon
    exact posne L hndL (L.length - 2) (L.length - 1) hn2len hlastlen (by omega)
      (hcon.trans hlast.symm)
  have hd'k2 : k ≥ 2 * L[L.length - 2]'hn2len := by
    obtain ⟨mm, hmm⟩ := hd'dvd
    have hmm2 : mm ≥ 2 := by
      rcases Nat.lt_or_ge mm 2 with h | h
      · rcases (show mm = 0 ∨ mm = 1 by omega) with rfl | rfl
        · omega
        · exact absurd (hmm.trans (mul_one _)).symm hd'nek
      · omega
    rw [hmm]
    have hmono := Nat.mul_le_mul_left (L[L.length - 2]'hn2len) hmm2
    omega
  have hL0 : L[0] = 1 := by simp [hLc]
  have hd'ne1 : L[L.length - 2]'hn2len ≠ 1 := by
    intro hcon
    exact posne L hndL 0 (L.length - 2) (by omega) hn2len (by omega)
      (hL0.trans hcon.symm)
  -- countP ≥ 2 via sublist
  set Z := List.zip L L.tail with hZdef
  have hZlen : Z.length = L.length - 1 := by
    rw [hZdef, List.length_zip]; simp only [List.length_tail]; omega
  have hZcons : Z = (1, d2) :: (List.zip (d2 :: rest) rest) := by
    rw [hZdef, hLc]; rfl
  have hzip : L.length - 2 < (List.zip L L.tail).length := by
    rw [List.length_zip]; simp only [List.length_tail]; omega
  have hz1 := List.getElem_zip (h := hzip)
  have geteq : ∀ (l : List ℕ) (i j : ℕ) (hij : i = j) (hi : i < l.length) (hj : j < l.length),
      l[i]'hi = l[j]'hj := by intro l i j hij _ _; subst hij; rfl
  have hz2 : L.tail[L.length - 2] = k :=
    Eq.trans (List.getElem_tail hn2t)
      (Eq.trans (geteq L (L.length - 2 + 1) (L.length - 1) (by omega) (by omega) (by omega)) hlast)
  have hmem2 : (L[L.length - 2]'hn2len, k) ∈ Z := by
    have hmz := List.getElem_mem hzip
    rw [hz1, hz2] at hmz
    exact hmz
  have hmem2' : (L[L.length - 2]'hn2len, k) ∈ List.zip (d2 :: rest) rest := by
    rw [hZcons] at hmem2
    rcases List.mem_cons.1 hmem2 with heq | hmem
    · exfalso
      exact hd'ne1 (congrArg Prod.fst heq)
    · exact hmem
  have hsub2 : [(1, d2), (L[L.length - 2]'hn2len, k)] <+ Z := by
    obtain ⟨M1, M2, hM⟩ := List.mem_iff_append.1 hmem2'
    rw [hZcons]
    refine List.Sublist.cons_cons _ ?_
    rw [hM]
    exact List.Sublist.append (List.nil_sublist M1)
      (List.Sublist.cons_cons _ (List.nil_sublist M2))
  have hcount := List.Sublist.countP_le (p := fun pair =>
      have d_k := pair.1;
      have d_k_succ := pair.2;
      decide (Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k)) hsub2
  have hkokd : Odd k := hLodd k hkL
  simp [List.countP_cons, List.countP_nil, Prod.fst, Prod.snd, hd2odd, hd2ge2,
    hkokd, hd'k2, decide_true, if_true, zero_add, add_zero] at hcount ⊢
  omega
