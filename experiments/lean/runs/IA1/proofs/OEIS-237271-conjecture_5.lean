import FormalConjectures.OEIS.«237271»

open OeisA237271 Nat Finset List

private theorem lem_jump_fwd {a b a' b' m : ℕ} (hm : 0 < m) (h1 : a * b' = m) (h2 : b * a' = m)
    (h : b > 2 * a) : b' > 2 * a' := by
  have ha : 0 < a := Nat.pos_of_ne_zero (fun h0 => by rw [h0, MulZeroClass.zero_mul] at h1; omega)
  have ha' : 0 < a' := Nat.pos_of_ne_zero (fun h0 => by rw [h0, MulZeroClass.mul_zero] at h2; omega)
  have k1 : b * a' > (2 * a) * a' := Nat.mul_lt_mul_of_pos_right h ha'
  have k2 : a * b' > a * (2 * a') := by
    calc a * b' = m := h1
      _ = b * a' := h2.symm
      _ > (2 * a) * a' := k1
      _ = a * (2 * a') := by ring
  exact Nat.lt_of_mul_lt_mul_left k2

private theorem lem_jump {a b a' b' m : ℕ} (hm : 0 < m) (h1 : a * b' = m) (h2 : b * a' = m) :
    b > 2 * a ↔ b' > 2 * a' :=
  ⟨lem_jump_fwd hm h1 h2,
    fun h => lem_jump_fwd hm (by rw [Nat.mul_comm]; exact h2) (by rw [Nat.mul_comm]; exact h1) h⟩

private theorem countP_zip_sum (D : List ℕ) :
    (zip D D.tail).countP (fun pr => pr.2 > 2 * pr.1) =
      ∑ i ∈ Finset.range (D.length - 1), (if D.getD (i + 1) 0 > 2 * D.getD i 0 then 1 else 0) := by
  induction D with
  | nil => simp
  | cons x r ih =>
    cases r with
    | nil => simp
    | cons y s =>
      have hz : zip (x :: y :: s) (x :: y :: s).tail = (x, y) :: zip (y :: s) s := rfl
      have hlen : (x :: y :: s).length - 1 = s.length + 1 := by simp
      rw [hz, List.countP_cons, hlen, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      simp only [List.getD_cons_succ] at ih
      rw [show (y :: s).length - 1 = s.length from by simp, List.tail_cons] at ih
      rw [ih]
      by_cases hc : y > 2 * x
      · rw [if_pos (show decide ((x, y).2 > 2 * (x, y).1) = true by simp [hc]), if_pos hc]
      · rw [if_neg (show ¬ (decide ((x, y).2 > 2 * (x, y).1) = true) by simp [hc]), if_neg hc]

private theorem even_sum_window {F : ℕ → ℕ} {L : ℕ}
    (hpair : ∀ i j, i + j = L - 2 → F i = F j)
    (hfix : ∀ i, 2 * i = L - 2 → F i = 0) :
    Even (∑ i ∈ Finset.range (L - 1), F i) := by
  have main : ∀ k lo, 2 * lo + k = L - 1 → Even (∑ i ∈ Finset.range k, F (lo + i)) := by
    intro k
    induction k using Nat.strong_induction_on
    next k ih =>
      intro lo hlo
      match k, hlo with
      | 0, _ => simp
      | 1, _ =>
        rw [show 1 = 0 + 1 from by rfl, Finset.sum_range_succ, Finset.sum_range_zero]
        have h0 : F (lo + 0) = 0 := hfix lo (by omega)
        rw [h0]
        simp
      | (k2 + 2), _ =>
        rw [show k2 + 2 = (k2 + 1) + 1 from by omega, Finset.sum_range_succ, Finset.sum_range_succ',
          show (lo + 0) = lo from by omega]
        have hpair' : F (lo + (k2 + 1)) = F lo := hpair (lo + (k2 + 1)) lo (by omega)
        rw [hpair']
        have hshift : ∑ i ∈ Finset.range k2, F (lo + (i + 1))
            = ∑ i ∈ Finset.range k2, F (lo + 1 + i) :=
          Finset.sum_congr rfl fun i _ => congrArg F (by omega)
        rw [hshift]
        have hinner := ih k2 (by omega) (lo + 1) (by omega)
        rcases hinner with ⟨w, hw⟩
        rw [hw]
        exact ⟨w + F lo, by omega⟩
  have hfin := main (L - 1) 0 (by omega)
  simpa using hfin

theorem swarm_proof (n : ℕ) (hn : 0 < n) : Odd (a (n * (2 * n - 1))) := by
  dsimp only [a]
  set m := n * (2 * n - 1) with hm
  have hmpos : 0 < m := Nat.mul_pos hn (by omega)
  have hmne : m ≠ 0 := by omega
  set D : List ℕ := m.divisors.sort (· ≤ ·) with hD
  set L := D.length with hL
  have hS : D.SortedLE := (Finset.pairwise_sort _ _).sortedLE
  have hmemD : ∀ d, d ∈ D ↔ d ∣ m ∧ 0 < d := by
    intro d
    constructor
    · intro hd
      obtain ⟨d1, _⟩ := Nat.mem_divisors.mp ((Finset.mem_sort (· ≤ ·)).mp hd)
      exact ⟨d1, Nat.pos_of_dvd_of_pos d1 hmpos⟩
    · intro hc
      exact (Finset.mem_sort (· ≤ ·)).mpr (Nat.mem_divisors.mpr ⟨hc.1, by omega⟩)
  have hfd : ∀ d ∈ D, (m / d) ∣ m ∧ m / (m / d) = d := by
    intro d hd
    have hd' := (hmemD d).mp hd
    exact ⟨Nat.div_dvd_of_dvd hd'.1, Nat.div_div_self hd'.1 hmne⟩
  set f : ℕ → ℕ := fun d => m / d with hf
  have hinj : ∀ x y, x ∣ m → 0 < x → y ∣ m → 0 < y → f x = f y → x = y := by
    intro x y hx hx0 hy hy0 hxy
    have hxy' : m / x = m / y := hxy
    have hx1 : m / (m / x) = x := Nat.div_div_self hx hmne
    have hy1 : m / (m / y) = y := Nat.div_div_self hy hmne
    rw [← hx1, ← hy1, hxy']
  have hDnodup : D.Nodup := Finset.sort_nodup _ _
  have hmono : ∀ a b, a ∈ D → b ∈ D → b ≤ a → m / a ≤ m / b := by
    intro a b ha hb hba
    have hcalc : (m / a) * b ≤ m := by
      calc (m / a) * b ≤ (m / a) * a := Nat.mul_le_mul_left _ hba
        _ = m := Nat.div_mul_cancel ((hmemD a).mp ha).1
    exact (Nat.le_div_iff_mul_le ((hmemD b).mp hb).2).mpr hcalc
  have hpw : ∀ (l : List ℕ), (∀ u ∈ l, u ∈ D) → List.Pairwise (fun p q => p ≥ q) l →
      List.Pairwise (fun p q => p ≤ q) (l.map f) := by
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons x r ih =>
      intro hsub hl
      obtain ⟨hhd, htl⟩ := List.pairwise_cons.mp hl
      exact List.Pairwise.cons
        (fun y hy => by
          obtain ⟨y', hy', hyf⟩ := List.mem_map.mp hy
          rw [← hyf]
          exact hmono x y' (hsub x (by simp)) (hsub y' (by simp [hy'])) (hhd y' hy'))
        (ih (fun u hu => hsub u (by simp [hu])) htl)
  have hEsorted : (D.reverse.map f).SortedLE :=
    (hpw D.reverse (fun u hu => List.mem_reverse.mp hu)
      (List.Pairwise.reverse (R := fun a b => a ≥ b) hS.pairwise)).sortedLE
  have hpermkey : ∀ (R T : List ℕ), (∀ u ∈ R, u ∈ D) → (∀ u ∈ T, u ∈ D) → R.Nodup → T.Nodup →
      (∀ z ∈ T, ∃ y ∈ R, f y = z) → (∀ u ∈ R, f u ∈ T) → (R.map f).Perm T := by
    intro R
    induction R with
    | nil =>
      intro T _ hTD _ hTn hex _
      cases T with
      | nil => rfl
      | cons z t => exact absurd (hex z (by simp)) (by simp)
    | cons x r ih =>
      intro T hsub hTD hn hTn hex hback
      have hfxT : f x ∈ T := hback x (by simp)
      have hfxD : x ∈ D := hsub x (by simp)
      have hxpos : 0 < x := ((hmemD x).mp hfxD).2
      have hxdvd : x ∣ m := ((hmemD x).mp hfxD).1
      have hnn : r.Nodup := (List.nodup_cons.mp hn).2
      have hne : f x ∉ T.erase (f x) :=
        fun hmem => (List.nodup_cons.mp ((List.perm_cons_erase hfxT).nodup_iff.mp hTn)).1 hmem
      have hex' : ∀ z ∈ T.erase (f x), ∃ y ∈ r, f y = z := by
        intro z hz
        have hzT : z ∈ T := List.mem_of_mem_erase hz
        obtain ⟨y, hy, hfy⟩ := hex z hzT
        refine ⟨y, ?_, hfy⟩
        rcases List.mem_cons.mp hy with hyx | hyr
        · rw [hyx] at hfy
          rw [← hfy] at hz
          exact absurd hz hne
        · exact hyr
      have hback' : ∀ u ∈ r, f u ∈ T.erase (f x) := by
        intro u hu
        have huD : u ∈ D := hsub u (by simp [hu])
        have hupos : 0 < u := ((hmemD u).mp huD).2
        have hudvd : u ∣ m := ((hmemD u).mp huD).1
        have hufx : f u ≠ f x := by
          intro heq
          have hux : u = x := hinj u x hudvd hupos hxdvd hxpos heq
          rw [hux] at hu
          exact (List.nodup_cons.mp hn).1 hu
        exact (List.mem_erase_of_ne hufx).mpr (hback u (by simp [hu]))
      have inner : (r.map f).Perm (T.erase (f x)) :=
        ih (T.erase (f x))
          (fun u hu => hsub u (by simp [hu]))
          (fun u hu => hTD u (List.mem_of_mem_erase hu))
          hnn (List.Nodup.erase (f x) hTn) hex' hback'
      exact (List.Perm.cons (f x) inner).trans (List.perm_cons_erase hfxT).symm
  have hperm : (D.reverse.map f).Perm D :=
    hpermkey D.reverse D
      (fun u hu => List.mem_reverse.mp hu)
      (fun u hu => hu)
      (List.nodup_reverse.mpr hDnodup)
      hDnodup
      (fun z hz => ⟨m / z,
        List.mem_reverse.mpr ((hmemD (m / z)).mpr ⟨(hfd z hz).1,
          Nat.pos_of_dvd_of_pos (hfd z hz).1 hmpos⟩),
        Nat.div_div_self ((hmemD z).mp hz).1 hmne⟩)
      (fun u hu =>
        (hmemD (m / u)).mpr ⟨(hfd u (List.mem_reverse.mp hu)).1,
          Nat.pos_of_dvd_of_pos ((hfd u (List.mem_reverse.mp hu)).1) hmpos⟩)
  have hE : D.reverse.map f = D := List.Perm.eq_of_sortedLE hEsorted hS hperm
  have hlenE : (D.reverse.map f).length = D.length := by
    rw [List.length_map, List.length_reverse]
  have hlenr : D.reverse.length = D.length := List.length_reverse
  have hconv : ∀ (l : List ℕ) j (hj : j < l.length), l.getD j 0 = l[j] :=
    fun l j hj => List.getD_eq_getElem l 0 hj
  have hEgetD : ∀ j, (D.reverse.map f).getD j 0 = D.getD j 0 := by
    intro j; rw [hE]
  have hrevD : ∀ j, j < D.length → D.reverse.getD j 0 = D.getD (D.length - 1 - j) 0 := by
    intro j hj
    rw [hconv D.reverse j (by rw [hlenr]; exact hj),
      hconv D (D.length - 1 - j) (by omega),
      List.getElem_reverse (by rw [hlenr]; exact hj)]
  have hmapgetD : ∀ j, j < D.length → (D.reverse.map f).getD j 0 = f (D.reverse.getD j 0) := by
    intro j hj
    rw [hconv (D.reverse.map f) j (by rw [hlenE]; exact hj), List.getElem_map,
      ← hconv D.reverse j (by rw [hlenr]; exact hj)]
  have hsym : ∀ j, j < D.length → D.getD j 0 * D.getD (D.length - 1 - j) 0 = m := by
    intro j hj
    have h1 : f (D.reverse.getD j 0) = D.getD j 0 := by
      rw [← hmapgetD j hj, hEgetD j]
    have h2 : f (D.reverse.getD j 0) = m / D.getD (D.length - 1 - j) 0 := by
      rw [hrevD j hj]
    have h3 : D.getD j 0 = m / D.getD (D.length - 1 - j) 0 := by rw [← h1, h2]
    have hmem2 : D.getD (D.length - 1 - j) 0 ∈ D := by
      rw [hconv D (D.length - 1 - j) (by omega)]
      exact List.getElem_mem (by omega)
    rw [h3, Nat.div_mul_cancel (((hmemD _).mp hmem2).1)]
  have hmn : m / n = 2 * n - 1 := Nat.div_eq_of_eq_mul_left hn (by rw [hm, Nat.mul_comm])
  have key : ∀ d d' (hp : (d, d') ∈ List.zip D D.tail), (Odd d' ∧ d' ≥ 2 * d) ↔ 2 * d < d' := by
    intro d d' hp
    obtain ⟨i, hi, hz⟩ := List.mem_iff_getElem.mp hp
    rw [List.getElem_zip] at hz
    have hzl : (D.zip D.tail).length = D.tail.length := by
      rw [List.length_zip, List.length_tail]
      exact Nat.min_eq_right (Nat.sub_le _ _)
    have htail : i < D.tail.length := by rw [← hzl]; exact hi
    have hi1 : i + 1 < D.length := by
      rw [List.length_tail] at htail; omega
    rw [List.getElem_tail htail] at hz
    rw [Prod.mk.injEq] at hz
    obtain ⟨hd, hd'⟩ := hz
    have hdL : d' ∈ D := by rw [← hd']; exact List.getElem_mem hi1
    obtain ⟨hddvd, hdne⟩ := Nat.mem_divisors.mp ((Finset.mem_sort (· ≤ ·)).mp hdL)
    have hnoBetween : ∀ e ∈ D, d < e → e < d' → False := by
      intro e he h1 h2
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
      rcases Nat.lt_or_ge j (i + 1) with hjlt | hjge
      · have hle : D[j] ≤ D[i] := hS.getElem_le_getElem_of_le (by omega)
        omega
      · have hle : D[i + 1] ≤ D[j] := hS.getElem_le_getElem_of_le (by omega)
        omega
    constructor
    · rintro ⟨hod, hge⟩
      refine lt_of_le_of_ne hge ?_
      intro heq
      obtain ⟨k, hk⟩ := hod
      omega
    · intro hlt
      refine ⟨?_, by omega⟩
      rcases Nat.even_or_odd d' with hE | hO
      · exfalso
        obtain ⟨t, ht2⟩ := hE
        have ht0 : 0 < t := by omega
        have hd2 : 2 * t ∣ m := Nat.dvd_trans (⟨1, by omega⟩ : 2 * t ∣ d') hddvd
        have htdvd : t ∣ m := Nat.dvd_trans (⟨2, by omega⟩ : t ∣ 2 * t) hd2
        have htL : t ∈ D :=
          (Finset.mem_sort (· ≤ ·)).mpr (Nat.mem_divisors.mpr ⟨htdvd, by omega⟩)
        exact hnoBetween t htL (by omega) (by rw [ht2]; omega)
      · exact hO
  have hgoalP : (zip D D.tail).countP
      (fun pair => let d_k := pair.fst; let d_k_succ := pair.snd;
        Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k)
      = (zip D D.tail).countP (fun pr => pr.2 > 2 * pr.1) := by
    refine List.countP_congr fun x hx => ?_
    obtain ⟨d, d'⟩ := x
    by_cases hlt : 2 * d < d'
    · have h2 := (key d d' hx).mpr hlt
      simp [h2, hlt]
    · have h2 : ¬ (Odd d' ∧ d' ≥ 2 * d) := fun hc => hlt ((key d d' hx).mp hc)
      simp [h2, hlt]
  have hFpair : ∀ i j, i + j = D.length - 2 →
      (if D.getD (i + 1) 0 > 2 * D.getD i 0 then 1 else 0)
      = (if D.getD (j + 1) 0 > 2 * D.getD j 0 then 1 else 0) := by
    intro i j hij
    rcases Nat.lt_or_ge (i + 1) D.length with hiL | hiL
    · have h1 : D.getD i 0 * D.getD (D.length - 1 - i) 0 = m := hsym i (by omega)
      have h2 : D.getD (i + 1) 0 * D.getD (D.length - 1 - (i + 1)) 0 = m :=
        hsym (i + 1) (by omega)
      have hjx : D.length - 1 - (i + 1) = j := by omega
      rw [hjx] at h2
      have hiff : (D.getD (i + 1) 0 > 2 * D.getD i 0) ↔
          (D.getD (D.length - 1 - i) 0 > 2 * D.getD j 0) := lem_jump hmpos h1 h2
      have hj1 : j + 1 = D.length - 1 - i := by omega
      rw [hj1]
      by_cases h : D.getD (i + 1) 0 > 2 * D.getD i 0
      · have hq := hiff.mp h
        rw [if_pos h, if_pos hq]
      · have hq : ¬ (D.getD (D.length - 1 - i) 0 > 2 * D.getD j 0) :=
          fun hc => h (hiff.mpr hc)
        rw [if_neg h, if_neg hq]
    · have hzd1 : D.getD (i + 1) 0 = 0 := List.getD_eq_default D 0 (by omega)
      have hzd2 : D.getD (j + 1) 0 = 0 := List.getD_eq_default D 0 (by omega)
      have hn1 : ¬ (D.getD (i + 1) 0 > 2 * D.getD i 0) := by rw [hzd1]; omega
      have hn2 : ¬ (D.getD (j + 1) 0 > 2 * D.getD j 0) := by rw [hzd2]; omega
      rw [if_neg hn1, if_neg hn2]
  have hFfix : ∀ i, 2 * i = D.length - 2 →
      (if D.getD (i + 1) 0 > 2 * D.getD i 0 then 1 else 0) = 0 := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) D.length with hiL | hiL
    · have hidxeq : D.length - 1 - i = i + 1 := by omega
      have hcc0 : D.getD i 0 * D.getD (D.length - 1 - i) 0 = m := hsym i (by omega)
      have hcc : D.getD i 0 * D.getD (i + 1) 0 = m := by rw [← hidxeq]; exact hcc0
      have hcD : D.getD i 0 ∈ D := by
        rw [hconv D i (by omega)]
        exact List.getElem_mem (by omega)
      have hc'D : D.getD (i + 1) 0 ∈ D := by
        rw [hconv D (i + 1) (by omega)]
        exact List.getElem_mem (by omega)
      have hcpos : 0 < D.getD i 0 := ((hmemD _).mp hcD).2
      have hc'pos : 0 < D.getD (i + 1) 0 := ((hmemD _).mp hc'D).2
      have hnD : n ∈ D :=
        (hmemD n).mpr ⟨by rw [hm]; exact Nat.dvd_mul_right n (2 * n - 1), hn⟩
      obtain ⟨j0, hj0, hj0n⟩ := List.mem_iff_getElem.mp hnD
      rcases Nat.lt_or_ge j0 (i + 1) with hcase | hcase
      · have hle0 : D[j0] ≤ D.getD i 0 := by
          rw [hconv D i (by omega)]
          exact hS.getElem_le_getElem_of_le (by omega)
        rw [hj0n] at hle0
        have hnc : n ≤ D.getD i 0 := hle0
        have hle : D.getD i 0 * D.getD (i + 1) 0 ≤ D.getD i 0 * (2 * n - 1) := by
          calc D.getD i 0 * D.getD (i + 1) 0 = m := hcc
            _ = n * (2 * n - 1) := hm
            _ ≤ D.getD i 0 * (2 * n - 1) := Nat.mul_le_mul hnc (Nat.le_refl _)
        have hc'le : D.getD (i + 1) 0 ≤ 2 * n - 1 :=
          Nat.le_of_mul_le_mul_left hle hcpos
        have hno : ¬ (D.getD (i + 1) 0 > 2 * D.getD i 0) := by omega
        rw [if_neg hno]
      · have hle1 : D.getD (i + 1) 0 ≤ D[j0] := by
          rw [hconv D (i + 1) (by omega)]
          exact hS.getElem_le_getElem_of_le (by omega)
        rw [hj0n] at hle1
        have hc'len : D.getD (i + 1) 0 ≤ n := hle1
        have hcmul : D.getD i 0 = m / D.getD (i + 1) 0 :=
          (Nat.div_eq_of_eq_mul_left hc'pos hcc.symm).symm
        have hge : m / n ≤ m / D.getD (i + 1) 0 := by
          rw [Nat.le_div_iff_mul_le hc'pos]
          calc (m / n) * D.getD (i + 1) 0 = (2 * n - 1) * D.getD (i + 1) 0 := by rw [hmn]
            _ ≤ (2 * n - 1) * n := Nat.mul_le_mul_left (2 * n - 1) hc'len
            _ = n * (2 * n - 1) := Nat.mul_comm _ _
            _ = m := hm.symm
        have hcge : 2 * n - 1 ≤ D.getD i 0 := by rw [hcmul, ← hmn]; exact hge
        have hno : ¬ (D.getD (i + 1) 0 > 2 * D.getD i 0) := by omega
        rw [if_neg hno]
    · have hzd : D.getD (i + 1) 0 = 0 := List.getD_eq_default D 0 (by omega)
      have hn : ¬ (D.getD (i + 1) 0 > 2 * D.getD i 0) := by rw [hzd]; omega
      rw [if_neg hn]
  have hev := even_sum_window (F := fun i => if D.getD (i + 1) 0 > 2 * D.getD i 0 then 1 else 0)
    (L := D.length) hFpair hFfix
  rcases hev with ⟨w, hw⟩
  have hw2 : ∑ i ∈ Finset.range (D.length - 1),
      (if D.getD (i + 1) 0 > 2 * D.getD i 0 then 1 else 0) = w + w := hw
  rw [hgoalP, countP_zip_sum D, hw2]
  exact ⟨w, by omega⟩