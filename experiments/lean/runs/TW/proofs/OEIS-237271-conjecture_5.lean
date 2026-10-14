import FormalConjectures.OEIS.«237271»

open OeisA237271 Nat Finset List

private lemma pw_mono {l : List ℕ} (hp : l.Pairwise (· ≤ ·)) {i j : ℕ}
    (hij : i ≤ j) (hj : j < l.length) : l[i] ≤ l[j] := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons a t ih =>
    match i, j with
    | 0, 0 => exact le_rfl
    | 0, j + 1 =>
      have hjt : j < t.length := by simpa using hj
      have hle := (List.pairwise_cons.mp hp).1 (t[j]) (List.getElem_mem (h := hjt))
      exact Nat.le_trans hle (by simpa using ih (List.pairwise_cons.mp hp).2 (Nat.zero_le j) hjt)
    | i + 1, 0 => omega
    | i + 1, j + 1 =>
      have hjt : j < t.length := by simpa using hj
      exact ih (List.pairwise_cons.mp hp).2 (by simpa using hij) hjt

private lemma pw_strict {l : List ℕ} (hp : l.Pairwise (· ≤ ·)) (hnd : l.Nodup)
    {i j : ℕ} (hij : i < j) (hj : j < l.length) : l[i] < l[j] := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons a t ih =>
    match i, j with
    | 0, 0 => omega
    | 0, j + 1 =>
      have hjt : j < t.length := by simpa using hj
      have hle := (List.pairwise_cons.mp hp).1 (t[j]) (List.getElem_mem (h := hjt))
      rcases Nat.eq_or_lt_of_le hle with h | h
      · subst h
        exact absurd (List.getElem_mem (h := hjt)) (List.nodup_cons.mp hnd).1
      · exact h
    | i + 1, 0 => omega
    | i + 1, j + 1 =>
      have hjt : j < t.length := by simpa using hj
      exact ih (List.pairwise_cons.mp hp).2 (List.nodup_cons.mp hnd).2 (by simpa using hij) hjt

private lemma mem_zip_imp {l : List ℕ} {x y : ℕ} (h : (x, y) ∈ l.zip l.tail) :
    ∃ i, i + 1 < l.length ∧ l[i]? = some x ∧ l[i + 1]? = some y := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    rcases t with _ | ⟨b, s⟩
    · simp at h
    · simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        exact ⟨0, by simp, by simp [h1], by simp [h2]⟩
      · have h' : (x, y) ∈ (b :: s).zip (b :: s).tail := by simpa using h
        obtain ⟨i, hi1, hi2, hi3⟩ := ih h'
        refine ⟨i + 1, ?_, ?_, ?_⟩
        · simp only [List.length_cons] at hi1 ⊢; omega
        · simp only [List.getElem?_cons_succ]; exact hi2
        · simp only [List.getElem?_cons_succ]; exact hi3

private lemma div_strict_rev {k x y : ℕ} (hk : 0 < k) (hx : x ∣ k) (hy : y ∣ k) (hxy : x < y) :
    k / y < k / x := by
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [h0] at hx; omega
    · exact h0
  have h1 : k / y ≤ k / x := Nat.div_le_div_left (Nat.le_of_lt hxy) hx0
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · exfalso
    have hy2 := Nat.div_div_self hy (ne_of_gt hk)
    have hx2 := Nat.div_div_self hx (ne_of_gt hk)
    rw [h] at hy2
    have hyx : y = x := by rw [← hy2]; exact hx2
    omega
  · exact h

private lemma zip_tail_mem {l : List ℕ} {i : ℕ} (h : i + 1 < l.length) :
    (l[i], l[i + 1]) ∈ l.zip l.tail := by
  induction l generalizing i with
  | nil => simp at h
  | cons a t ih =>
    rcases t with _ | ⟨b, s⟩
    · simp at h
    · cases i with
      | zero => simp
      | succ i =>
        have hl : i + 1 < (b :: s).length := by simpa using h
        have hind := ih hl
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
        exact Or.inr hind

theorem swarm_proof (n : ℕ) (hn : 0 < n) : Odd (a (n * (2 * n - 1))) := by
  set k := n * (2 * n - 1) with hkdef
  have hk : 0 < k := by
    have h2n : 0 < 2 * n - 1 := by omega
    exact Nat.mul_pos hn h2n
  set D : List ℕ := (k.divisors.sort (· ≤ ·)) with hD
  have hpw : D.Pairwise (· ≤ ·) := Finset.pairwise_sort k.divisors (· ≤ ·)
  have hnd : D.Nodup := Finset.sort_nodup k.divisors (· ≤ ·)
  have hmemD : ∀ d, d ∈ D ↔ (d ∣ k ∧ 0 < d) := by
    intro d
    rw [hD, Finset.mem_sort, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, hne⟩
      refine ⟨hd, ?_⟩
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · rw [h0] at hd; omega
      · exact h0
    · rintro ⟨hd, hpos⟩
      exact ⟨hd, Nat.ne_of_gt hk⟩
  have hDlen1 : 0 < D.length := List.length_pos_of_mem ((hmemD 1).mpr ⟨one_dvd k, Nat.one_pos⟩)
  have hDpos : ∀ j (hj : j < D.length), 0 < D[j]'(by omega) := by
    intro j hj
    exact ((hmemD (D[j]'(by omega))).mp (List.getElem_mem (h := hj))).2
  have hlast : D[D.length - 1] = k := by
    have hkD : k ∈ D := by
      rw [hD, Finset.mem_sort]
      exact Nat.mem_divisors.mpr ⟨dvd_refl k, Nat.ne_of_gt hk⟩
    obtain ⟨j, hj, hval⟩ := List.getElem_of_mem hkD
    have hle := pw_mono hpw (by omega : j ≤ D.length - 1) (by omega)
    have hdvd := ((hmemD (D[D.length - 1]'(by omega))).mp
      (List.getElem_mem (h := by omega))).1
    have hkle := Nat.le_of_dvd (by omega : 0 < k) hdvd
    omega
  set f : ℕ → ℕ := fun d => k / d with hf
  have hslt : D.SortedLT := List.sortedLT_iff_pairwise.mpr ((List.pairwise_iff_getElem).mpr
    (fun i j hi hj hlt => pw_strict hpw hnd hlt hj))
  have hsgt : (D.map f).SortedGT := by
    rw [List.sortedGT_iff_pairwise, List.pairwise_iff_getElem]
    intro i j hi hj hlt
    have hlenf : (D.map f).length = D.length := List.length_map f
    have hiD : i < D.length := by omega
    have hjD : j < D.length := by omega
    have hdvd_i : D[i] ∣ k := ((hmemD (D[i])).mp (List.getElem_mem (h := hiD))).1
    have hdvd_j : D[j] ∣ k := ((hmemD (D[j])).mp (List.getElem_mem (h := hjD))).1
    have hval := pw_strict hpw hnd hlt hjD
    rw [List.getElem_map f (h := hi), List.getElem_map f (h := hj)]
    exact div_strict_rev hk hdvd_i hdvd_j hval
  have hmemiff : ∀ z, z ∈ D.map f ↔ z ∈ D := by
    intro z
    constructor
    · intro hm
      rw [List.mem_map] at hm
      obtain ⟨w, hw, hfw⟩ := hm
      have hd := ((hmemD w).mp hw).1
      have hz2 : 0 < k / w := by
        have hmul := Nat.mul_div_cancel' hd
        rcases Nat.eq_zero_or_pos (k / w) with h0 | h0
        · rw [h0] at hmul; omega
        · exact h0
      rw [← hfw]
      exact (hmemD _).mpr ⟨Nat.div_dvd_of_dvd hd, hz2⟩
    · intro hz
      have hd := ((hmemD z).mp hz).1
      have hz2 : 0 < k / z := by
        have hmul := Nat.mul_div_cancel' hd
        rcases Nat.eq_zero_or_pos (k / z) with h0 | h0
        · rw [h0] at hmul; omega
        · exact h0
      have hmem : k / z ∈ D := (hmemD _).mpr ⟨Nat.div_dvd_of_dvd hd, hz2⟩
      rw [List.mem_map]
      refine ⟨k / z, hmem, ?_⟩
      show f (k / z) = z
      exact Nat.div_div_self hd (Nat.ne_of_gt hk)
  have hrev : D = (D.map f).reverse :=
    List.SortedLT.eq_reverse_of_mem_iff_of_sortedGT (fun z => (hmemiff z).symm) hslt hsgt
  have hcomp : ∀ j (hj : j < D.length),
      k / (D[j]'(by omega)) = (D[D.length - 1 - j]'(by omega)) := by
    intro j hj
    have hlenf : (D.map f).length = D.length := List.length_map f
    have hrevlen : (D.map f).reverse.length = D.length := by
      rw [List.length_reverse, hlenf]
    have hjrev : j < (D.map f).reverse.length := by omega
    have hopt : D[j]? = (D.map f).reverse[j]? := congrArg (fun l => l[j]?) hrev
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjrev] at hopt
    simp only [Option.some.injEq] at hopt
    have h5 : (D.map f)[(D.map f).length - 1 - j]'(by omega) =
        f (D[D.length - 1 - j]'(by omega)) := by
      have h6 : (D.map f)[(D.map f).length - 1 - j]'(by omega) =
          (D.map f)[D.length - 1 - j]'(by omega) := by
        congr 1
        omega
      rw [h6]
      exact List.getElem_map f
    have hd : D[D.length - 1 - j] ∣ k :=
      ((hmemD _).mp (List.getElem_mem (h := by omega))).1
    show k / (D[j]'hj) = (D[D.length - 1 - j]'(by omega))
    rw [hopt, List.getElem_reverse hjrev, h5]
    exact Nat.div_div_self hd (Nat.ne_of_gt hk)

  -- zip list
  set Z : List (ℕ × ℕ) := D.zip D.tail with hZ
  have hZlen : Z.length = D.length - 1 := by
    rw [hZ, List.length_zip, List.length_tail]
    omega
  have hZj? : ∀ j (hj : j < Z.length),
      Z[j]? = some (D[j]'(by omega), D[j + 1]'(by omega)) := by
    intro j hj
    have hz1 : Z[j]? = (D.zip D.tail)[j]? := congrArg (fun l => l[j]?) hZ.symm
    have hjz : j < (D.zip D.tail).length := by rw [← hZ]; exact hj
    have hjtl : j < D.tail.length := by rw [List.length_tail]; omega
    rw [hz1]
    rw [List.getElem?_eq_getElem hjz]
    rw [List.getElem_zip]
    rw [List.getElem_tail hjtl]
  have hZj : ∀ j (hj : j < Z.length),
      (Z[j]'(by omega)) = (D[j]'(by omega), D[j + 1]'(by omega)) := by
    intro j hj
    have h1 := List.getElem?_eq_getElem hj
    have h2 := hZj? j hj
    have h : some (Z[j]'(by omega)) = some (D[j]'(by omega), D[j + 1]'(by omega)) :=
      h1.symm.trans h2
    simpa using h
  set invq : ℕ × ℕ → ℕ × ℕ := fun q => (k / q.2, k / q.1) with hphi
  have hrevZ : Z.map invq = Z.reverse := by
    apply List.ext_getElem?'
    intro i hi
    rw [List.getElem?_map]
    by_cases hiZ : i < Z.length
    · have hc1 := hcomp (i + 1) (by omega)
      have hc2 := hcomp i (by omega)
      rw [hZj? i (by omega : i < Z.length), List.getElem?_reverse hiZ,
        hZj? (Z.length - 1 - i) (by omega : Z.length - 1 - i < Z.length)]
      simp only [Option.map_some, hphi, Option.some.injEq, Prod.mk.injEq]
      rw [hc1, hc2]
      constructor
      · congr 1; omega
      · congr 1; omega
    · have hzr : Z.reverse.length = Z.length := List.length_reverse
      rw [List.getElem?_eq_none_iff.mpr (by omega : Z.length ≤ i),
        List.getElem?_eq_none_iff.mpr (by omega : Z.reverse.length ≤ i)]
      rfl
  -- divisibility helper
  have hkey : ∀ a b : ℕ, 0 < a → 2 * a ≤ b → a ∣ k → b ∣ k → 2 * (k / b) ≤ k / a := by
    intro a b ha hab hak hbk
    have h1 : k / b ≤ k / (2 * a) :=
      Nat.div_le_div_left (by omega : 2 * a ≤ b) (by omega : 0 < 2 * a)
    have h2 := Nat.mul_div_le k (2 * a)
    have h3 : a * (2 * (k / (2 * a))) ≤ k := by
      calc a * (2 * (k / (2 * a))) = (2 * a) * (k / (2 * a)) := by ring
        _ ≤ k := h2
    have hka : a * (k / a) = k := Nat.mul_div_cancel' hak
    have h3' : a * (2 * (k / (2 * a))) ≤ a * (k / a) := by
      rw [hka]
      exact h3
    have h4 := Nat.le_of_mul_le_mul_left h3' ha
    omega
  -- invq maps Z to Z
  have hmemZinvq : ∀ x ∈ Z, invq x ∈ Z := by
    intro x hx
    obtain ⟨j, hj1, hj2, hj3⟩ := mem_zip_imp hx
    have hjD1 : j < D.length := by omega
    have hjD2 : j + 1 < D.length := by omega
    rw [List.getElem?_eq_getElem hjD1] at hj2
    rw [List.getElem?_eq_getElem hjD2] at hj3
    simp only [Option.some.injEq] at hj2 hj3
    -- hj2 : D[j] = x.1, hj3 : D[j+1] = x.2
    have hzmem := zip_tail_mem (l := D) (i := D.length - 2 - j) (by omega)
    have e0 : D.length - 2 - j + 1 = D.length - 1 - j := by omega
    simp only [e0] at hzmem
    have hc1 := hcomp (j + 1) hjD2
    have hc2 := hcomp j hjD1
    have hpair : invq x = (D[D.length - 2 - j]'(by omega), D[D.length - 1 - j]'(by omega)) := by
      rw [hphi]
      show (k / x.2, k / x.1) = _
      rw [← hj3, ← hj2, hc1, hc2]
      have e1 : D.length - 1 - (j + 1) = D.length - 2 - j := by omega
      simp only [e1]
    rw [hpair]
    exact hzmem
  -- invq is an involution on Z
  have hphi2 : ∀ x ∈ Z, invq (invq x) = x := by
    intro x hx
    obtain ⟨j, hj1, hj2, hj3⟩ := mem_zip_imp hx
    have hjD1 : j < D.length := by omega
    have hjD2 : j + 1 < D.length := by omega
    rw [List.getElem?_eq_getElem hjD1] at hj2
    rw [List.getElem?_eq_getElem hjD2] at hj3
    simp only [Option.some.injEq] at hj2 hj3
    have hdvd1 : x.1 ∣ k := by
      rw [← hj2]
      exact ((hmemD _).mp (List.getElem_mem (h := hjD1))).1
    have hdvd2 : x.2 ∣ k := by
      rw [← hj3]
      exact ((hmemD _).mp (List.getElem_mem (h := hjD2))).1
    rw [hphi]
    show (k / (k / x.1), k / (k / x.2)) = x
    rw [Nat.div_div_self hdvd1 (Nat.ne_of_gt hk), Nat.div_div_self hdvd2 (Nat.ne_of_gt hk)]
  -- forward invariance of the qualifying predicate
  have hPfwd : ∀ x ∈ Z, (Odd x.2 ∧ x.2 ≥ 2 * x.1) →
      (Odd (invq x).2 ∧ (invq x).2 ≥ 2 * (invq x).1) := by
    intro x hx hp
    obtain ⟨hodd, h2a⟩ := hp
    obtain ⟨j, hj1, hj2, hj3⟩ := mem_zip_imp hx
    have hjD1 : j < D.length := by omega
    have hjD2 : j + 1 < D.length := by omega
    rw [List.getElem?_eq_getElem hjD1] at hj2
    rw [List.getElem?_eq_getElem hjD2] at hj3
    simp only [Option.some.injEq] at hj2 hj3
    have hdvd1 : D[j] ∣ k := ((hmemD _).mp (List.getElem_mem (h := hjD1))).1
    have hdvd2 : D[j + 1] ∣ k := ((hmemD _).mp (List.getElem_mem (h := hjD2))).1
    have hpos1 : 0 < D[j] := hDpos j hjD1
    rw [← hj2] at h2a
    rw [← hj3] at h2a hodd
    have hodd' : D[j + 1] % 2 = 1 := Nat.odd_iff.mp hodd
    have hratio : 2 * (k / D[j + 1]) ≤ k / D[j] :=
      hkey D[j] D[j + 1] hpos1 h2a hdvd1 hdvd2
    have hpar : (k / D[j]) % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (k / D[j]) with hc | hc
      · exfalso
        obtain ⟨t, ht⟩ := (Nat.dvd_iff_mod_eq_zero).mpr hc
        have hka : D[j] * (k / D[j]) = k := Nat.mul_div_cancel' hdvd1
        have hw : (2 * D[j]) ∣ k := by
          refine ⟨t, ?_⟩
          calc k = D[j] * (k / D[j]) := hka.symm
            _ = D[j] * (2 * t) := by rw [ht]
            _ = 2 * D[j] * t := by ring
        have hwmem : 2 * D[j] ∈ D :=
          (hmemD _).mpr ⟨hw, Nat.mul_pos (by omega) hpos1⟩
        obtain ⟨p, hp1, hp2⟩ := List.getElem_of_mem hwmem
        have hp_gt : j < p := by
          by_contra hc2
          have hle0 := pw_mono hpw (by omega : p ≤ j) (by omega : j < D.length)
          rw [hp2] at hle0
          omega
        have hle := pw_mono hpw (by omega : j + 1 ≤ p) (by omega : p < D.length)
        rw [hp2] at hle
        omega
      · exact hc
    rw [hphi]
    show Odd (k / x.1) ∧ k / x.1 ≥ 2 * (k / x.2)
    rw [← hj2, ← hj3]
    exact ⟨Nat.odd_iff.mpr hpar, hratio⟩
  -- half-split lemma
  have hdrops : Z.drop (D.length / 2) = ((Z.take ((D.length - 1) / 2)).map invq).reverse := by
    have hld : (Z.drop (D.length / 2)).length = (D.length - 1) / 2 := by
      rw [List.length_drop, hZlen]
      omega
    have hlt2 : ((Z.take ((D.length - 1) / 2)).map invq).reverse.length = (D.length - 1) / 2 := by
      rw [List.length_reverse, List.length_map, List.length_take, hZlen]
      omega
    apply List.ext_getElem?'
    intro i hi
    have hih : i < (D.length - 1) / 2 := by omega
    have hZih : i < Z.length := by omega
    have hDih : D.length / 2 + i < D.length := by omega
    have hDih2 : D.length / 2 + i + 1 < D.length := by omega
    have hDh : (D.length - 1) / 2 - 1 - i < (D.length - 1) / 2 := by omega
    have hDhZ : (D.length - 1) / 2 - 1 - i < Z.length := by omega
    have hmlen : ((Z.take ((D.length - 1) / 2)).map invq).length = (D.length - 1) / 2 := by
      rw [List.length_map, List.length_take, hZlen]
      omega
    rw [List.getElem?_drop, hZj? (D.length / 2 + i) (by omega : D.length / 2 + i < Z.length),
      List.getElem?_reverse (by omega : i < ((Z.take ((D.length - 1) / 2)).map invq).length),
      List.getElem?_map, List.getElem?_take, hmlen,
      if_pos (by omega : (D.length - 1) / 2 - 1 - i < (D.length - 1) / 2),
      hZj? ((D.length - 1) / 2 - 1 - i) hDhZ]
    simp only [Option.map_some, hphi, Option.some.injEq, Prod.mk.injEq]
    have hc1 := hcomp ((D.length - 1) / 2 - i) (by omega)
    have hc2 := hcomp ((D.length - 1) / 2 - 1 - i) (by omega)
    have eidx : (D.length - 1) / 2 - 1 - i + 1 = (D.length - 1) / 2 - i := by omega
    simp only [eidx]
    rw [hc1, hc2]
    constructor
    · congr 1; omega
    · congr 1; omega
  -- middle element cannot qualify
  have hmid : ∀ j (hj : j < Z.length), Z.length % 2 = 1 → j = (Z.length - 1) / 2 →
      decide (Odd Z[j].2 ∧ Z[j].2 ≥ 2 * Z[j].1) = false := by
    intro j hj hodd hjeq
    by_contra hcon
    rw [Bool.not_eq_false, decide_eq_true_eq] at hcon
    rw [hZj j hj] at hcon
    dsimp only at hcon
    obtain ⟨hodd2, h2a⟩ := hcon
    have hmEven : D.length % 2 = 0 := by omega
    have hDh : j < D.length := by omega
    have hDh1 : j + 1 < D.length := by omega
    have hdvdh : D[j] ∣ k := ((hmemD _).mp (List.getElem_mem (h := hDh))).1
    have hc0 := hcomp j hDh
    have hidx : D.length - 1 - j = j + 1 := by omega
    simp only [hidx] at hc0
    have hab : D[j] * D[j + 1] = k := by
      rw [← hc0]
      exact Nat.mul_div_cancel' hdvdh
    have hklt : k < 2 * (n * n) := by
      have h2n : n * (2 * n - 1) < n * (2 * n) := Iff.mpr (Nat.mul_lt_mul_left (by omega)) (by omega)
      have e : n * (2 * n) = 2 * (n * n) := by ring
      rw [hkdef]
      omega
    -- D[j] < n
    have ha_n : D[j] < n := by
      by_contra hcn1
      have hnle : n ≤ D[j] := by omega
      have hs3 : 2 * (n * n) ≤ 2 * (D[j] * D[j]) := by
        refine Nat.mul_le_mul_left 2 ?_
        exact Nat.mul_le_mul hnle hnle
      have hs1 : 2 * (D[j] * D[j]) ≤ k := by
        calc 2 * (D[j] * D[j]) = D[j] * (2 * D[j]) := by ring
          _ ≤ D[j] * D[j + 1] := Nat.mul_le_mul_left _ h2a
          _ = k := hab
      omega
    -- 2*n-1 < D[j+1]
    have hb_t : 2 * n - 1 < D[j + 1] := by
      by_contra hcn2
      have hble : D[j + 1] ≤ 2 * n - 1 := by omega
      have hsq1 : 2 * k ≤ D[j + 1] * D[j + 1] := by
        calc 2 * k = D[j + 1] * (2 * D[j]) := by rw [← hab]; ring
          _ ≤ D[j + 1] * D[j + 1] := Nat.mul_le_mul_left _ h2a
      have hsq2 : (2 * n - 1) * (2 * n - 1) < 2 * k := by
        have hmon : (2 * n - 1) * (2 * n - 1) < (2 * n - 1) * (2 * n) :=
          Iff.mpr (Nat.mul_lt_mul_left (by omega)) (by omega)
        have e : (2 * n - 1) * (2 * n) = 2 * k := by rw [hkdef]; ring
        omega
      have hsq3 : D[j + 1] * D[j + 1] ≤ (2 * n - 1) * (2 * n - 1) :=
        Nat.mul_le_mul hble hble
      omega
    -- n ≥ 2
    have hn2 : 2 ≤ n := by
      by_contra hcn
      have hn1 : n = 1 := by omega
      subst hn1
      have hk1 : k = 1 := by rw [hkdef]
      have hstr := pw_strict hpw hnd (show 0 < 1 by omega) (show 1 < D.length by omega)
      have hle := pw_mono hpw (by omega : 1 ≤ D.length - 1) (by omega : D.length - 1 < D.length)
      rw [hlast, hk1] at hle
      have hd0 : 0 < D[0] := hDpos 0 (by omega)
      have hd1 : 0 < D[1] := hDpos 1 (by omega)
      omega
    have hnD : n ∈ D := (hmemD n).mpr ⟨⟨2 * n - 1, hkdef⟩, hn⟩
    obtain ⟨p, hp1, hp2⟩ := List.getElem_of_mem hnD
    have hp_gt : j < p := by
      by_contra hcp
      have hle0 := pw_mono hpw (by omega : p ≤ j) (by omega : j < D.length)
      rw [hp2] at hle0
      omega
    have hle2 := pw_mono hpw (by omega : j + 1 ≤ p) (by omega : p < D.length)
    rw [hp2] at hle2
    omega
  -- backward direction of predicate invariance
  have hPiff : ∀ x ∈ Z, decide (Odd (invq x).2 ∧ (invq x).2 ≥ 2 * (invq x).1) =
      decide (Odd x.2 ∧ x.2 ≥ 2 * x.1) := by
    intro x hx
    by_cases hxP : Odd x.2 ∧ x.2 ≥ 2 * x.1
    · rw [decide_eq_true_eq.mpr hxP, decide_eq_true_eq.mpr (hPfwd x hx hxP)]
    · have hnot : ¬ (Odd (invq x).2 ∧ (invq x).2 ≥ 2 * (invq x).1) := by
        intro hQ
        have h2 := hPfwd (invq x) (hmemZinvq x hx) hQ
        rw [hphi2 x hx] at h2
        exact hxP h2
      have e1 : decide (Odd x.2 ∧ x.2 ≥ 2 * x.1) = false := by simp [hxP]
      have e2 : decide (Odd (invq x).2 ∧ (invq x).2 ≥ 2 * (invq x).1) = false := by
        simp [hnot]
      rw [e2, e1]
  -- drop half counts like take half
  have hc1c : (Z.drop (D.length / 2)).countP
        (fun q : ℕ × ℕ => decide (Odd q.2 ∧ q.2 ≥ 2 * q.1)) =
      (Z.take ((D.length - 1) / 2)).countP
        (fun q : ℕ × ℕ => decide (Odd q.2 ∧ q.2 ≥ 2 * q.1)) := by
    rw [hdrops, List.countP_reverse, List.countP_map]
    apply List.countP_congr
    intro a ha
    have haZ : a ∈ Z := List.mem_of_mem_take ha
    constructor
    · intro h
      have h' : decide (Odd (invq a).2 ∧ (invq a).2 ≥ 2 * (invq a).1) = true := h
      rw [hPiff a haZ] at h'
      exact h'
    · intro h
      show decide (Odd (invq a).2 ∧ (invq a).2 ≥ 2 * (invq a).1) = true
      rw [← hPiff (invq a) (hmemZinvq a haZ), hphi2 a haZ]
      exact h
  -- count is even
  have heven : ∃ c : ℕ, Z.countP (fun q : ℕ × ℕ => decide (Odd q.2 ∧ q.2 ≥ 2 * q.1)) = 2 * c := by
    rw [← List.take_append_drop (D.length / 2) Z, List.countP_append]
    rcases Nat.even_or_odd Z.length with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hZeven : Z.length % 2 = 0 := by rw [hm]; omega
      refine ⟨(Z.take (D.length / 2)).countP
        (fun q : ℕ × ℕ => decide (Odd q.2 ∧ q.2 ≥ 2 * q.1)), ?_⟩
      have eidx : D.length / 2 = (D.length - 1) / 2 := by omega
      rw [hc1c]
      simp only [eidx]
      omega
    · have hZodd : Z.length % 2 = 1 := by rw [hm]; omega
      refine ⟨(Z.take ((D.length - 1) / 2)).countP
        (fun q : ℕ × ℕ => decide (Odd q.2 ∧ q.2 ≥ 2 * q.1)), ?_⟩
      have eidx : D.length / 2 = (D.length - 1) / 2 + 1 := by omega
      have hzh : (D.length - 1) / 2 < Z.length := by omega
      have htk : Z.take (D.length / 2) =
          Z.take ((D.length - 1) / 2) ++ [Z[(D.length - 1) / 2]] := by
        rw [eidx, List.take_add_one]
        simp only [List.getElem?_eq_getElem hzh, Option.toList_some]
      rw [htk, List.countP_append, List.countP_cons,
        hmid ((D.length - 1) / 2) (by omega) hZodd (by omega), hc1c]
      simp
      omega
  -- assembly
  simp only [a]
  rw [← hD, ← hZ]
  obtain ⟨c, hc⟩ := heven
  rw [hc]
  exact Nat.odd_iff.mpr (by omega)
