import FormalConjectures.OEIS.«237271»

open Nat Finset List

theorem mem_fst_zip (L : List ℕ) {x y : ℕ} (h : (x, y) ∈ L.zip L.tail) : x ∈ L := by
  induction L with
  | nil => simp at h
  | cons u t ih =>
    cases t with
    | nil => simp [zip] at h
    | cons v ts =>
      simp only [tail] at h
      rw [zip_cons_cons] at h
      rcases mem_cons.1 h with hp | hp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        exact List.mem_cons.2 (Or.inl rfl)
      · exact mem_cons_of_mem _ (ih hp)

theorem mem_snd_zip (L : List ℕ) {x y : ℕ} (h : (x, y) ∈ L.zip L.tail) : y ∈ L := by
  induction L with
  | nil => simp at h
  | cons u t ih =>
    cases t with
    | nil => simp [zip] at h
    | cons v ts =>
      simp only [tail] at h
      rw [zip_cons_cons] at h
      rcases mem_cons.1 h with hp | hp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        exact mem_cons_of_mem _ (mem_cons_self ..)
      · exact mem_cons_of_mem _ (ih hp)

theorem no_between {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) {x y : ℕ}
    (hm : (x, y) ∈ L.zip L.tail) {z : ℕ} (hz : z ∈ L) (hxz : x < z) : y ≤ z := by
  induction L generalizing x y with
  | nil => simp at hm
  | cons u t ih =>
    cases t with
    | nil => simp [zip] at hm
    | cons v ts =>
      simp only [tail] at hm
      rw [zip_cons_cons] at hm
      rcases mem_cons.1 hm with hp | hp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        rcases List.mem_cons.1 hz with hz0 | hz1
        · omega
        · obtain ⟨_, hpt⟩ := List.pairwise_cons.1 hs
          rcases List.mem_cons.1 hz1 with hz2 | hz3
          · rw [hz2]
          · obtain ⟨hv, _⟩ := List.pairwise_cons.1 hpt
            exact hv z hz3
      · obtain ⟨hu, hpt⟩ := List.pairwise_cons.1 hs
        rcases List.mem_cons.1 hz with hz0 | hz1
        · have hxu := hu x (mem_fst_zip (v :: ts) hp)
          omega
        · exact ih hpt hp hz1 hxz


theorem mem_snd_tail_zip (L : List ℕ) {x y : ℕ} (h : (x, y) ∈ L.zip L.tail) : y ∈ L.tail := by
  induction L with
  | nil => simp at h
  | cons u t ih =>
    cases t with
    | nil => simp [zip] at h
    | cons v ts =>
      simp only [tail] at h
      rw [zip_cons_cons] at h
      rcases mem_cons.1 h with hp | hp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        simp only [List.tail]
        exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (ih hp)

theorem zip_lt {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) (hn : L.Nodup) {x y : ℕ}
    (hm : (x, y) ∈ L.zip L.tail) : x < y := by
  induction L generalizing x y with
  | nil => simp at hm
  | cons u t ih =>
    cases t with
    | nil => simp [zip] at hm
    | cons v ts =>
      simp only [tail] at hm
      rw [zip_cons_cons] at hm
      rcases mem_cons.1 hm with hp | hp
      · obtain ⟨hu, _⟩ := List.pairwise_cons.1 hs
        obtain ⟨hnd, _⟩ := List.nodup_cons.1 hn
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        have h1 : x ≤ y := hu y (by simp)
        have hxy : x ≠ y := by
          intro he
          exact hnd (by rw [he]; exact List.mem_cons.2 (Or.inl rfl))
        omega
      · obtain ⟨hu, hpt⟩ := List.pairwise_cons.1 hs
        obtain ⟨_, hnd⟩ := List.nodup_cons.1 hn
        have hxz : x ∈ v :: ts := mem_fst_zip (v :: ts) hp
        have hvx : v ≤ x := by
          rcases List.mem_cons.1 hxz with heq | hxs
          · omega
          · obtain ⟨hv, _⟩ := List.pairwise_cons.1 hpt
            exact hv x hxs
        exact ih hpt hnd hp

theorem mem_zip_intro {L : List ℕ} (hs : L.Pairwise (· ≤ ·)) (hn : L.Nodup) {a b : ℕ} (ha : a ∈ L)
    (hb : b ∈ L.tail) (hlt : a < b) (hadj : ∀ z ∈ L, ¬ (a < z ∧ z < b)) :
    (a, b) ∈ L.zip L.tail := by
  induction L with
  | nil => simp at ha hb
  | cons u t ih =>
    cases t with
    | nil => simp at hb
    | cons v ts =>
      obtain ⟨hu, hpt⟩ := List.pairwise_cons.1 hs
      obtain ⟨hnd, hndt⟩ := List.nodup_cons.1 hn
      rcases List.mem_cons.1 ha with heqa | ha'
      · rcases List.mem_cons.1 hb with heqb | hb'
        · rw [← heqa, ← heqb]
          exact List.mem_cons.2 (Or.inl rfl)
        · obtain ⟨hv2, _⟩ := List.pairwise_cons.1 hpt
          have hvb : v ≤ b := hv2 b hb'
          have huv2 : u ≤ v := hu v (by simp)
          have huv : u ≠ v := by
            intro h
            apply hnd
            rw [h]
            exact List.mem_cons.2 (Or.inl rfl)
          have hvb2 : v ≠ b := by
            intro h
            exact (List.nodup_cons.1 hndt).1 (by rw [h]; exact hb')
          exact absurd (hadj v (List.mem_cons_of_mem u (by simp)) ⟨by omega, by omega⟩) (by simp)
      · rcases List.mem_cons.1 hb with heqb | hb'
        · exfalso
          rw [heqb] at hlt
          have hvx : v ≤ a := by
            rcases List.mem_cons.1 ha' with heq | hxs
            · omega
            · obtain ⟨hv, _⟩ := List.pairwise_cons.1 hpt
              exact hv a hxs
          omega
        · exact mem_cons_of_mem _ (ih hpt hndt ha' hb' (fun z hz => hadj z (mem_cons_of_mem _ hz)))

theorem nodup_zip_tail {L : List ℕ} (hn : L.Nodup) : (L.zip L.tail).Nodup := by
  induction L with
  | nil => simp
  | cons u t ih =>
    cases t with
    | nil => simp [zip]
    | cons v ts =>
      simp only [tail]
      rw [zip_cons_cons]
      obtain ⟨hnd, hndt⟩ := List.nodup_cons.1 hn
      refine List.nodup_cons.2 ⟨?_, ih hndt⟩
      intro hmem
      have h2 : v ∈ ts := by
        have := mem_snd_tail_zip (v :: ts) hmem
        simpa using this
      exact absurd h2 (List.nodup_cons.1 hndt).1


def phiFn (m : ℕ) (x : ℕ × ℕ) : ℕ × ℕ := (m / x.2, m / x.1)

def jbf (x : ℕ × ℕ) : Bool := decide (x.2 > 2 * x.1)

def gbf (m : ℕ) (x : ℕ × ℕ) : Bool := decide (x.2 < m / x.1)

def hbf (m : ℕ) (x : ℕ × ℕ) : Bool := decide (m / x.1 < x.2)

lemma divSelfInv {m d : ℕ} (hd : d ∣ m) (hm : m ≠ 0) : m / (m / d) = d := by
  have e1 : d * (m / d) = m := Nat.mul_div_cancel' hd
  have e2 : (m / d) * (m / (m / d)) = m := Nat.mul_div_cancel' (Nat.div_dvd_of_dvd hd)
  have hp2 : 0 < m / d := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd) hm.bot_lt
  have he : (m / d) * (m / (m / d)) = (m / d) * d := by
    rw [e2, Nat.div_mul_cancel hd]
  have he2 : (m / (m / d)) * (m / d) = d * (m / d) := by
    rw [Nat.mul_comm (m / (m / d)) (m / d), Nat.mul_comm d (m / d)]
    exact he
  exact Nat.eq_of_mul_eq_mul_right hp2 he2

lemma dvdDivAnti {m a b : ℕ} (ha : a ∣ m) (hb : b ∣ m) (hm : 0 < m) (h : a ≤ b) : m / b ≤ m / a := by
  have e1 : a * (m / a) = m := Nat.mul_div_cancel' ha
  have e2 : b * (m / b) = m := Nat.mul_div_cancel' hb
  have h5 : a * (m / a) ≤ b * (m / a) := Nat.mul_le_mul_right (m / a) h
  rw [e1] at h5
  have h6 : b * (m / b) ≤ b * (m / a) := by
    rw [e2]
    exact h5
  exact Nat.le_of_mul_le_mul_left h6 (Nat.pos_of_dvd_of_pos hb hm)

lemma dvdDivAntiStrict {m a b : ℕ} (ha : a ∣ m) (hb : b ∣ m) (hm : 0 < m) (h : a < b) : m / b < m / a := by
  have h1 : m / b ≤ m / a := dvdDivAnti ha hb hm (Nat.le_of_lt h)
  by_contra hcon
  push_neg at hcon
  have heq : m / a = m / b := Nat.le_antisymm hcon h1
  have e1 : a * (m / a) = m := Nat.mul_div_cancel' ha
  have e2 : b * (m / b) = m := Nat.mul_div_cancel' hb
  have hb' : 0 < m / b := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hb) hm
  rw [heq] at e1
  have hba : a * (m / b) = b * (m / b) := by rw [e1, e2]
  have hab : a = b := Nat.eq_of_mul_eq_mul_right hb' hba
  omega

lemma mem_tail_ne_one {L : List ℕ} (hpw : L.Pairwise (· ≤ ·)) (hpos : ∀ d ∈ L, 0 < d) {x : ℕ}
    (hx : x ∈ L) (hone : 1 ∈ L) (hne : x ≠ 1) : x ∈ L.tail := by
  cases L with
  | nil => simp at hx
  | cons u t =>
    obtain ⟨hu, _⟩ := List.pairwise_cons.1 hpw
    rcases List.mem_cons.1 hx with he | hx'
    · rw [he] at hne
      rcases List.mem_cons.1 hone with he1 | hone'
      · rw [he1] at hne
        exact absurd rfl hne
      · exfalso
        have h1 : u ≤ 1 := hu 1 hone'
        have h2 : 0 < u := hpos u (List.mem_cons.2 (Or.inl rfl))
        omega
    · exact hx'

lemma countP_split2 {p q r : ℕ × ℕ → Bool} {l : List (ℕ × ℕ)}
    (hexcl : ∀ x ∈ l, ¬(q x = true ∧ r x = true))
    (hcover : ∀ x ∈ l, (p x = true ↔ q x = true ∨ r x = true)) :
    l.countP p = l.countP q + l.countP r := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ih := ih (fun x hx => hexcl x (List.mem_cons_of_mem _ hx))
      (fun x hx => hcover x (List.mem_cons_of_mem _ hx))
    cases hq : q a <;> cases hr : r a <;> simp_all [List.countP_cons] <;> omega

lemma countP_zero_of {p : ℕ × ℕ → Bool} {l : List (ℕ × ℕ)} (h : ∀ x ∈ l, p x = false) :
    l.countP p = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ht : ∀ x ∈ t, p x = false := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.countP_cons, h a (List.mem_cons.2 (Or.inl rfl)), ih ht]
    simp


theorem swarm_proof (n : ℕ) (hn : 0 < n) : Odd (OeisA237271.a (n * (2 * n - 1))) := by
  generalize hM : n * (2 * n - 1) = m
  have hmpos : 0 < m := by rw [← hM]; exact Nat.mul_pos hn (by omega)
  have hm0 : m ≠ 0 := hmpos.ne'
  obtain ⟨L, hL⟩ : ∃ L, m.divisors.sort (· ≤ ·) = L := ⟨_, rfl⟩
  have hpw : L.Pairwise (· ≤ ·) := by
    rw [← hL]
    exact Finset.pairwise_sort _ (· ≤ ·)
  have hnd : L.Nodup := by
    rw [← hL]
    exact Finset.sort_nodup _ (· ≤ ·)
  have hmL : ∀ d ∈ L, d ∣ m ∧ 0 < d := by
    intro d hd
    rw [← hL] at hd
    have := Nat.mem_divisors.1 ((Finset.mem_sort (· ≤ ·)).1 hd)
    exact ⟨this.1, Nat.pos_of_dvd_of_pos this.1 this.2.bot_lt⟩
  have hLmem : ∀ d, d ∣ m → d ∈ L := by
    intro d hdd
    rw [← hL]
    exact (Finset.mem_sort (· ≤ ·)).2 (Nat.mem_divisors.2 ⟨hdd, hm0⟩)
  have h1L : 1 ∈ L := hLmem 1 (by rw [← hM]; exact one_dvd _)
  have hndZ : (L.zip L.tail).Nodup := nodup_zip_tail hnd

  -- Phi maps Z to Z
  have hΦmem : ∀ x ∈ L.zip L.tail, phiFn m x ∈ L.zip L.tail := by
    intro x hx
    obtain ⟨hd1, hp1⟩ := hmL _ (mem_fst_zip L hx)
    obtain ⟨hd2, hp2⟩ := hmL _ (mem_snd_zip L hx)
    have hlt : x.1 < x.2 := zip_lt hpw hnd hx
    have hAmem : m / x.2 ∈ L := hLmem _ (Nat.div_dvd_of_dvd hd2)
    have hBmem : m / x.1 ∈ L := hLmem _ (Nat.div_dvd_of_dvd hd1)
    have hBne : m / x.1 ≠ 1 := by
      intro he
      have e1 : x.1 * (m / x.1) = m := Nat.mul_div_cancel' hd1
      rw [he, Nat.mul_one] at e1
      have h2m : x.2 ≤ m := Nat.le_of_dvd hmpos hd2
      omega
    have hBtail : m / x.1 ∈ L.tail :=
      mem_tail_ne_one hpw (fun d hd => (hmL d hd).2) hBmem h1L hBne
    have hAgt : m / x.2 < m / x.1 := dvdDivAntiStrict hd1 hd2 hmpos hlt
    refine mem_zip_intro hpw hnd hAmem hBtail hAgt ?_
    intro z hz hpair
    obtain ⟨hzl, hzg⟩ := hpair
    obtain ⟨hdz, hpz⟩ := hmL z hz
    have hwmem : m / z ∈ L := hLmem _ (Nat.div_dvd_of_dvd hdz)
    have h1 : x.1 ≤ m / z := by
      have := dvdDivAnti hdz (Nat.div_dvd_of_dvd hd1) hmpos (Nat.le_of_lt hzg)
      rwa [divSelfInv hd1 hm0] at this
    have h2 : m / z ≤ x.2 := by
      have := dvdDivAnti (Nat.div_dvd_of_dvd hd2) hdz hmpos (Nat.le_of_lt hzl)
      rwa [divSelfInv hd2 hm0] at this
    rcases Nat.eq_or_lt_of_le h1 with he | hlt1
    · have hz1 : z = m / x.1 := by
        have := divSelfInv hdz hm0
        rw [← he] at this
        exact this.symm
      omega
    · rcases Nat.eq_or_lt_of_le h2 with he2 | hlt2
      · have hz2 : z = m / x.2 := by
          have := divSelfInv hdz hm0
          rw [he2] at this
          exact this.symm
        omega
      · have hn1 := no_between hpw hx hwmem hlt1
        have hzq : z = m / x.2 := by
          have hdz2 := divSelfInv hdz hm0
          rw [show m / z = x.2 from Nat.le_antisymm h2 hn1] at hdz2
          exact hdz2.symm
        omega

  have hΦinv : ∀ x ∈ L.zip L.tail, phiFn m (phiFn m x) = x := by
    intro x hx
    obtain ⟨hd1, _⟩ := hmL _ (mem_fst_zip L hx)
    obtain ⟨hd2, _⟩ := hmL _ (mem_snd_zip L hx)
    have e1 := divSelfInv hd1 hm0
    have e2 := divSelfInv hd2 hm0
    simp only [phiFn]
    exact Prod.ext e1 e2

  -- Finset route to the count identity
  have hcount : ∀ q : ℕ × ℕ → Bool,
      (L.zip L.tail).countP q = ((L.zip L.tail).toFinset.filter (fun x => q x = true)).card := by
    intro q
    have hndf : ((L.zip L.tail).filter q).Nodup := hndZ.filter q
    have hbr : ((L.zip L.tail).filter q).toFinset
        = (L.zip L.tail).toFinset.filter (fun x => q x = true) := by
      ext x
      simp [List.mem_filter]
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup hndf, hbr]

  have hinjOn : Set.InjOn (phiFn m) ↑(L.zip L.tail).toFinset := by
    intro x hx y hy heq
    have hxZ : x ∈ L.zip L.tail := List.mem_toFinset.1 (Finset.mem_coe.1 hx)
    have hyZ : y ∈ L.zip L.tail := List.mem_toFinset.1 (Finset.mem_coe.1 hy)
    have h1 := hΦinv x hxZ
    rw [heq] at h1
    rw [hΦinv y hyZ] at h1
    exact h1.symm

  have hSsub : ((L.zip L.tail).toFinset.image (phiFn m)) ⊆ (L.zip L.tail).toFinset := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact List.mem_toFinset.2 (hΦmem x (List.mem_toFinset.1 hx))

  have hScard : ((L.zip L.tail).toFinset.image (phiFn m)).card = (L.zip L.tail).toFinset.card :=
    Finset.card_image_of_injOn hinjOn

  have hSeq : ((L.zip L.tail).toFinset.image (phiFn m)) = (L.zip L.tail).toFinset :=
    Finset.eq_of_subset_of_card_le hSsub (hScard ▸ Nat.le_refl _)

  have hpaircard : ((L.zip L.tail).toFinset.filter (fun x => (jbf x && hbf m x) = true)).card
      = ((L.zip L.tail).toFinset.filter (fun x => (jbf x && gbf m x) = true)).card := by
    have hc0 : ((L.zip L.tail).toFinset.filter (fun x => (jbf x && hbf m x) = true)).card
        = (((L.zip L.tail).toFinset.image (phiFn m)).filter
            (fun x => (jbf x && hbf m x) = true)).card := by rw [hSeq]
    rw [hc0, Finset.filter_image]
    rw [Finset.card_image_of_injOn
      (hinjOn.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))]
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro x hx
    have hxZ : x ∈ L.zip L.tail := List.mem_toFinset.1 hx
    obtain ⟨hd1, hp1⟩ := hmL _ (mem_fst_zip L hxZ)
    obtain ⟨hd2, hp2⟩ := hmL _ (mem_snd_zip L hxZ)
    have e1 : x.1 * (m / x.1) = m := Nat.mul_div_cancel' hd1
    have e2 : x.2 * (m / x.2) = m := Nat.mul_div_cancel' hd2
    have pA : 0 < m / x.1 := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd1) hmpos
    have pB : 0 < m / x.2 := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd2) hmpos
    have ej : jbf (phiFn m x) = true ↔ jbf x = true := by
      show (decide (m / x.1 > 2 * (m / x.2)) = true) ↔ (decide (x.2 > 2 * x.1) = true)
      rw [decide_eq_true_eq, decide_eq_true_eq]
      have hEq : x.1 * (m / x.1) = x.2 * (m / x.2) := by rw [e1, e2]
      have hRe : 2 * x.1 * (m / x.2) = x.1 * (2 * (m / x.2)) := by ring
      constructor
      · intro h
        have t1 : x.1 * (2 * (m / x.2)) < x.1 * (m / x.1) := Nat.mul_lt_mul_of_pos_left h hp1
        rw [← hRe] at t1
        have t2 := Nat.lt_of_lt_of_eq t1 hEq
        exact Nat.lt_of_mul_lt_mul_right t2
      · intro h
        have t1 : 2 * x.1 * (m / x.2) < x.2 * (m / x.2) := Nat.mul_lt_mul_of_pos_right h pB
        rw [hRe] at t1
        have t2 := Nat.lt_of_lt_of_eq t1 hEq.symm
        exact Nat.lt_of_mul_lt_mul_left t2
    have eh : hbf m (phiFn m x) = true ↔ gbf m x = true := by
      simp only [hbf, gbf, phiFn, decide_eq_true_eq, divSelfInv hd2 hm0]
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨ej.1 a, eh.1 b⟩
    · rintro ⟨a, b⟩
      exact ⟨ej.2 a, eh.2 b⟩

  -- fixed-point-free cells are empty
  have hF : ∀ x ∈ L.zip L.tail, ¬(jbf x = true ∧ x.2 = m / x.1) := by
    intro x hx hpair
    obtain ⟨h1, h2⟩ := hpair
    simp only [jbf, decide_eq_true_eq] at h1
    obtain ⟨hd1, hp1⟩ := hmL _ (mem_fst_zip L hx)
    obtain ⟨hd2, hp2⟩ := hmL _ (mem_snd_zip L hx)
    have e1 : x.1 * (m / x.1) = m := Nat.mul_div_cancel' hd1
    rw [← h2] at e1
    have hnL : n ∈ L := hLmem n (by rw [← hM]; exact Nat.dvd_mul_right n (2 * n - 1))
    have hnq : m / n = 2 * n - 1 := by
      rw [← hM]
      exact Nat.mul_div_cancel_left (2 * n - 1) hn
    have hx1n : x.1 < n := by
      by_contra hc
      push_neg at hc
      have t1 : n * (2 * n - 1) < n * x.2 :=
        Nat.mul_lt_mul_of_pos_left (by omega) hn
      have t2 : n * x.2 ≤ x.1 * x.2 := Nat.mul_le_mul_right x.2 hc
      have hslt : n * (2 * n - 1) < x.1 * x.2 := Nat.lt_of_lt_of_le t1 t2
      have hfin : n * (2 * n - 1) < m := Nat.lt_of_lt_of_eq hslt e1
      rw [← hM] at hfin
      exact absurd hfin (Nat.lt_irrefl _)
    have hxbound := no_between hpw hx hnL hx1n
    have hlow : 2 * n - 1 ≤ x.2 := by
      have := dvdDivAnti hd1 (by rw [← hM]; exact Nat.dvd_mul_right n (2 * n - 1)) hmpos (Nat.le_of_lt hx1n)
      rwa [hnq, ← h2] at this
    omega

  -- assemble: Even (countP jbf Z)
  have heven : ∃ c, (L.zip L.tail).countP jbf = 2 * c := by
    refine ⟨(L.zip L.tail).countP (fun x => jbf x && gbf m x), ?_⟩
    have s1 : (L.zip L.tail).countP jbf
        = (L.zip L.tail).countP (fun x => jbf x && gbf m x)
          + (L.zip L.tail).countP (fun x => jbf x && !gbf m x) := by
      refine countP_split2 ?_ ?_
      · intro x hx
        rcases hb : gbf m x <;> simp_all
      · intro x hx
        rcases hb : gbf m x <;> simp_all
    have s2 : (L.zip L.tail).countP (fun x => jbf x && !gbf m x)
        = (L.zip L.tail).countP (fun x => jbf x && hbf m x)
          + (L.zip L.tail).countP (fun x => jbf x && decide (x.2 = m / x.1)) := by
      refine countP_split2 ?_ ?_
      · intro x hx
        by_cases hb : jbf x = true
        · simp only [hb, Bool.true_and, hbf, decide_eq_true_eq]
          omega
        · simp [hb]
      · intro x hx
        by_cases hb : jbf x = true
        · simp only [hb, Bool.true_and, Bool.not_eq_true', gbf, hbf, decide_eq_true_eq,
            decide_eq_false_iff_not]
          omega
        · simp [hb]
    have s3 : (L.zip L.tail).countP (fun x => jbf x && hbf m x)
        = (L.zip L.tail).countP (fun x => jbf x && gbf m x) := by
      rw [hcount _, hcount _]
      exact hpaircard
    have s4 : (L.zip L.tail).countP (fun x => jbf x && decide (x.2 = m / x.1)) = 0 := by
      refine countP_zero_of ?_
      intro x hx
      by_cases hb1 : jbf x = true
      · by_cases hb2 : x.2 = m / x.1
        · exact absurd ⟨hb1, hb2⟩ (hF x hx)
        · simp [hb2]
      · simp [hb1]
    omega

  -- final: a m = 1 + count
  simp only [OeisA237271.a]
  rw [hL]
  have key : ∀ x ∈ L.zip L.tail,
      (decide (Odd x.2 ∧ x.2 ≥ 2 * x.1)) = true ↔ jbf x = true := by
    intro x hx
    rw [jbf]
    simp only [decide_eq_true_eq]
    have h1L2 : x.1 ∈ L := mem_fst_zip L hx
    have h2L2 : x.2 ∈ L := mem_snd_zip L hx
    have hd1 : x.1 ∣ m := (hmL _ h1L2).1
    have hd2 : x.2 ∣ m := (hmL _ h2L2).1
    have hp2 : 0 < x.2 := (hmL _ h2L2).2
    constructor
    · rintro ⟨hodd, hge⟩
      by_contra hc
      push_neg at hc
      have hxe : x.2 = 2 * x.1 := by omega
      rw [hxe] at hodd
      have := Nat.odd_iff.1 hodd
      omega
    · intro hgt
      refine ⟨?_, by omega⟩
      by_contra hev
      have hmod : x.2 % 2 = 0 := Nat.not_odd_iff.1 hev
      obtain ⟨w, hw⟩ : ∃ w, x.2 = 2 * w := ⟨x.2 / 2, by omega⟩
      have hwd : w ∣ x.2 := by
        rw [hw, Nat.mul_comm]
        exact Nat.dvd_mul_right w 2
      have hwn : w ∣ m := Nat.dvd_trans hwd hd2
      have hwL : w ∈ L := hLmem w hwn
      have hw1 : x.1 < w := by omega
      have hw2 : w < x.2 := by omega
      have := no_between hpw hx hwL hw1
      omega
  rw [List.countP_congr key]
  obtain ⟨c, hc⟩ := heven
  exact ⟨c, by omega⟩
