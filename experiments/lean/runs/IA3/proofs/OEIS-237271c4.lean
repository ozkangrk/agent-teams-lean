import FormalConjectures.OEIS.«237271»

/-! Swarm proof for OEIS A237271 conjecture_4: `Odd (a (n ^ 2))`.
Adjacent divisor pairs (d, e) with e > 2 * d are permuted by the
divisor-complement index involution i ↦ len - 2 - i; it has no fixed
point among good indices because the middle pair d * e = n ^ 2 of a
square is never good. -/

namespace S237271D

open List Finset Nat

set_option maxHeartbeats 512000

/-- Sorted list of divisors (abbreviation). -/
def D (N : ℕ) : List ℕ := OeisA237271.sortedDivisorsList N

/- ## Basic divisor-list facts -/

section Basic
variable {N : ℕ}

theorem D_mem (hN : 0 < N) : ∀ a, a ∈ D N ↔ a ∣ N := by
  intro a
  rw [D, OeisA237271.sortedDivisorsList, Finset.mem_sort (· ≤ ·), Nat.mem_divisors]
  exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩

theorem D_pair (N : ℕ) : (D N).Pairwise (· ≤ ·) := by
  show ((Nat.divisors N).sort (· ≤ ·)).Pairwise (· ≤ ·)
  exact Finset.pairwise_sort _ (· ≤ ·)

theorem D_nodup (N : ℕ) : (D N).Nodup := by
  show ((Nat.divisors N).sort (· ≤ ·)).Nodup
  exact Finset.sort_nodup _ (· ≤ ·)

theorem D_len_pos (hN : 0 < N) : 0 < (D N).length := by
  have h1 : 1 ∈ Nat.divisors N := Nat.one_mem_divisors.2 (Nat.ne_of_gt hN)
  have h2 : 1 ∈ D N := (Finset.mem_sort (· ≤ ·)).mpr h1
  exact List.length_pos_of_mem h2

theorem getD_mem {l : List ℕ} : ∀ {i : ℕ}, i < l.length → l.getD i 0 ∈ l := by
  intro i h
  rw [List.getD_eq_getElem l 0 h]
  exact List.getElem_mem h

end Basic

/- ## Pointwise helpers (as in the accepted conjecture_2 proof) -/

theorem countP_eq_of_forall {α : Type} : ∀ (l : List α) (p q : α → Bool),
    (∀ x ∈ l, p x = q x) → l.countP p = l.countP q := by
  intro l p q h
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : p x = q x := h x (List.mem_cons_self ..)
    simp only [List.countP_cons, hx]
    rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem mem_zip_tail : ∀ (l : List ℕ) (p : ℕ × ℕ), p ∈ l.zip l.tail → p.1 ∈ l ∧ p.2 ∈ l := by
  intro l
  induction l with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    rcases xs with _ | ⟨y, ys⟩
    · simp at hp
    · have hp' : p ∈ (x, y) :: (y :: ys).zip ys := by simpa [List.zip] using hp
      rcases List.mem_cons.mp hp' with hp2 | hp2
      · subst hp2; exact ⟨by simp, by simp⟩
      · exact ⟨List.mem_cons_of_mem _ (ih p hp2).1, List.mem_cons_of_mem _ (ih p hp2).2⟩

theorem no_between (l : List ℕ) : l.Pairwise (· ≤ ·) → ∀ p : ℕ × ℕ, p ∈ l.zip l.tail →
    ∀ m ∈ l, p.1 < m → m < p.2 → False := by
  induction l with
  | nil => intro _ p hp; simp at hp
  | cons x xs ih =>
    intro hl p hp m hm h1 h2
    rcases xs with _ | ⟨y, ys⟩
    · simp at hp
    · have hyy : ∀ a ∈ ys, y ≤ a := (List.pairwise_cons.mp ((List.pairwise_cons.mp hl).2)).1
      have hp' : p ∈ (x, y) :: (y :: ys).zip ys := by simpa [List.zip] using hp
      rcases List.mem_cons.mp hp' with hp2 | hp2
      · -- p = (x, y)
        subst hp2
        rcases List.mem_cons.mp hm with rfl | hm
        · omega
        · rcases List.mem_cons.mp hm with rfl | hm
          · omega
          · have hle := hyy m hm; omega
      · refine ih ((List.pairwise_cons.mp hl).2) p hp2 m ?_ h1 h2
        rcases List.mem_cons.mp hm with rfl | hm
        · obtain ⟨hp1, -⟩ := mem_zip_tail _ p hp2
          have hy1 : y ≤ p.1 := by
            rcases List.mem_cons.mp hp1 with rfl | hp1'
            · exact le_refl _
            · exact hyy p.1 hp1'
          have hxy : _ ≤ y := (List.pairwise_cons.mp hl).1 y (by simp)
          omega
        · exact hm

theorem odd_of_adj {n : ℕ} (p : ℕ × ℕ) (hp : p ∈ (D n).zip ((D n).tail))
    (hgt : p.2 > 2 * p.1) : Odd p.2 := by
  by_contra hE
  rw [Nat.odd_iff] at hE
  have hmem2 : p.2 ∈ D n := (mem_zip_tail _ p hp).2
  have hd2 : p.2 ∈ Nat.divisors n := (Finset.mem_sort (· ≤ ·)).mp hmem2
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp hd2
  obtain ⟨m, hpe⟩ : ∃ m, p.2 = 2 * m := ⟨p.2 / 2, by omega⟩
  have hmp2 : m ∣ p.2 := ⟨2, by omega⟩
  have hmd : m ∈ Nat.divisors n := Nat.mem_divisors.mpr ⟨Nat.dvd_trans hmp2 hdvd, hn0⟩
  have hmL : m ∈ D n := (Finset.mem_sort (· ≤ ·)).mpr hmd
  exact no_between (D n) (D_pair n) p hp m hmL (by omega) (by omega)

theorem a_eq (n : ℕ) : OeisA237271.a n = 1 + ((D n).zip (D n).tail).countP
    (fun p => decide (p.2 > 2 * p.1)) := by
  have key : ((D n).zip (D n).tail).countP (fun p => decide (Odd p.2 ∧ p.2 ≥ 2 * p.1))
      = ((D n).zip (D n).tail).countP (fun p => decide (p.2 > 2 * p.1)) :=
    countP_eq_of_forall _ _ _ fun p hp => by
      by_cases h : p.2 > 2 * p.1
      · rw [decide_eq_true h, decide_eq_true ⟨odd_of_adj p hp h, by omega⟩]
      · rw [decide_eq_false h, decide_eq_false (by
          rintro ⟨hodd, hge⟩
          rw [Nat.odd_iff] at hodd
          omega)]
  calc OeisA237271.a n = 1 + ((D n).zip (D n).tail).countP
        (fun p => decide (Odd p.2 ∧ p.2 ≥ 2 * p.1)) := rfl
    _ = 1 + ((D n).zip (D n).tail).countP (fun p => decide (p.2 > 2 * p.1)) := by rw [key]

/- ## Indexing bridge: zip with tail is a map over ranges -/

theorem range_succ_cons (m : ℕ) : List.range (m+1) = 0 :: (List.range m).map (·+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hA : List.range (m + 1 + 1) = List.range (m + 1) ++ [m + 1] := List.range_succ
    have hB : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    rw [hA]
    conv_lhs => rw [ih, List.cons_append]
    rw [hB, List.map_append, List.map_singleton]

theorem zip_map_range (l : List ℕ) :
    l.zip l.tail = (List.range (l.length - 1)).map (fun i => (l.getD i 0, l.getD (i+1) 0)) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · simp
    · have hL : (x :: y :: ys).zip ((x :: y :: ys).tail)
          = (x, y) :: ((y :: ys).zip ((y :: ys).tail)) := rfl
      rw [hL, ih]
      have hL1 : (x :: y :: ys).length = (y :: ys).length + 1 := by simp
      obtain ⟨k, hk⟩ : ∃ k, (y :: ys).length = k + 1 :=
        ⟨(y :: ys).length - 1, by simp only [List.length_cons]; omega⟩
      have hA : (y :: ys).length - 1 = k := by omega
      have hB : (x :: y :: ys).length - 1 = k + 1 := by omega
      rw [hA, hB, range_succ_cons, List.map_cons]
      have hxy : ((x :: y :: ys).getD 0 0, (x :: y :: ys).getD (0 + 1) 0) = (x, y) := by
        simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [hxy, List.cons.injEq, List.map_map]
      refine And.intro rfl ?_
      refine List.map_congr_left fun i _ => ?_
      simp [List.getD_cons_succ]

/- ## Divisor-complement symmetry -/

section Compl
variable {N : ℕ}

theorem compl_rev (hN : 0 < N) : ((D N).map (fun d => N / d)).reverse = D N := by
  have hnd : (D N).Nodup := D_nodup N
  have hp : (D N).Pairwise (· ≤ ·) := D_pair N
  have hp' := hp
  rw [List.pairwise_iff_getElem] at hp'
  have hle : (D N).SortedLE := hp.sortedLE
  have hlt : (D N).SortedLT := List.sortedLT_iff_nodup_and_sortedLE.mpr ⟨hnd, hle⟩
  have hmem : ∀ a, a ∈ D N ↔ a ∣ N := D_mem hN
  have hinj : ∀ x ∈ D N, ∀ y ∈ D N, N / x = N / y → x = y := by
    intro x hx y hy h
    have hxd := (hmem x).mp hx
    have hyd := (hmem y).mp hy
    have h1 := Nat.div_div_self hxd (by omega)
    have h2 := Nat.div_div_self hyd (by omega)
    rw [h, h2] at h1
    exact h1.symm
  have himg : ∀ d ∈ D N, N / d ∈ D N := fun d hd =>
    (hmem _).mpr (Nat.div_dvd_of_dvd ((hmem d).mp hd))
  have hnd' : ((D N).map (fun d => N / d)).reverse.Nodup := by
    refine List.nodup_reverse.mpr (hnd.map_on ?_)
    intro x hx y hy h
    exact hinj x hx y hy h
  have hlenM : ((D N).map (fun d => N / d)).length = (D N).length := List.length_map _
  have hpm : ((D N).map (fun d => N / d)).Pairwise (· ≥ ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < (D N).length := by omega
    have hj' : j < (D N).length := by omega
    have h1 : ((D N).map (fun d => N / d))[i] = N / (D N)[i] :=
      List.getElem_map (f := fun d => N / d) (i := i) (h := hi)
    have h2 : ((D N).map (fun d => N / d))[j] = N / (D N)[j] :=
      List.getElem_map (f := fun d => N / d) (i := j) (h := hj)
    rw [h1, h2]
    have hle' : (D N)[i] ≤ (D N)[j] := hp' _ _ hi' hj' hij
    have hpos : 0 < (D N)[i] :=
      Nat.pos_of_dvd_of_pos ((D_mem hN _).mp (List.getElem_mem hi')) hN
    exact Nat.div_le_div_left hle' hpos
  have hsort : ((D N).map (fun d => N / d)).reverse.SortedLT := by
    rw [List.sortedLT_iff_nodup_and_sortedLE]
    refine ⟨hnd', ?_⟩
    rw [List.sortedLE_iff_pairwise, List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hrev : ((D N).map (fun d => N / d)).reverse.length
        = ((D N).map (fun d => N / d)).length := List.length_reverse
    have e1 := List.getElem_reverse (l := (D N).map (fun d => N / d)) (i := i) hi
    have e2 := List.getElem_reverse (l := (D N).map (fun d => N / d)) (i := j) hj
    have hia : ((D N).map (fun d => N / d)).length - 1 - i
        < ((D N).map (fun d => N / d)).length := by omega
    have hja : ((D N).map (fun d => N / d)).length - 1 - j
        < ((D N).map (fun d => N / d)).length := by omega
    have e3 := List.getElem_map (f := fun d => N / d)
      (i := ((D N).map (fun d => N / d)).length - 1 - i) (h := hia)
    have e4 := List.getElem_map (f := fun d => N / d)
      (i := ((D N).map (fun d => N / d)).length - 1 - j) (h := hja)
    rw [e1, e2, e3, e4]
    have hcmp : (D N)[((D N).map (fun d => N / d)).length - 1 - j]
        ≤ (D N)[((D N).map (fun d => N / d)).length - 1 - i] :=
      hp' _ _ (by omega) (by omega) (by omega)
    have hpos : 0 < (D N)[((D N).map (fun d => N / d)).length - 1 - j] :=
      Nat.pos_of_dvd_of_pos ((D_mem hN _).mp (List.getElem_mem (by omega))) hN
    exact Nat.div_le_div_left hcmp hpos
  refine (hlt.eq_of_mem_iff hsort (fun a => ?_)).symm
  simp only [List.mem_reverse, List.mem_map]
  constructor
  · intro ha
    exact ⟨N / a, himg a ha, Nat.div_div_self ((hmem a).mp ha) (by omega)⟩
  · rintro ⟨d, hd, hd2⟩
    exact hd2 ▸ himg d hd

theorem compl_get (hN : 0 < N) (k : ℕ) (hk : k < (D N).length) :
    N / (D N).getD k 0 = (D N).getD ((D N).length - 1 - k) 0 := by
  have hlenM : ((D N).map (fun d => N / d)).length = (D N).length := List.length_map _
  have hk2 : k < ((D N).map (fun d => N / d)).length := by omega
  have hrev : k < (D N).reverse.length := by simp only [List.length_reverse]; omega
  have h1 : ((D N).map (fun d => N / d))[k] = N / (D N)[k]'(by omega) :=
    List.getElem_map (f := fun d => N / d) (i := k) (h := hk2)
  have hC : ((D N).map (fun d => N / d))[k] = (D N).reverse[k]'(hrev) := by
    have hlist : ((D N).map (fun d => N / d)) = (D N).reverse := by
      have h := compl_rev hN
      have h2 := congrArg List.reverse h
      rwa [List.reverse_reverse] at h2
    exact List.getElem_of_eq hlist hk2
  have h4 : (D N).reverse[k]'(hrev) = (D N)[(D N).length - 1 - k]'(by omega) :=
    List.getElem_reverse hrev
  rw [List.getD_eq_getElem (D N) 0 hk, List.getD_eq_getElem (D N) 0 (by omega), ← h1, hC, h4]

/-- Good-pair invariance under the complement index involution. -/
theorem good_inv (hN : 0 < N) (i : ℕ) (hi : i + 1 < (D N).length)
    (hgood : (D N).getD (i+1) 0 > 2 * (D N).getD i 0) :
    (D N).getD ((D N).length - 2 - i + 1) 0 > 2 * (D N).getD ((D N).length - 2 - i) 0 := by
  have hkm : i < (D N).length := by omega
  have hmemi : (D N).getD i 0 ∈ D N := getD_mem hkm
  have hmemj : (D N).getD (i+1) 0 ∈ D N := getD_mem hi
  have hdi : (D N).getD i 0 ∣ N := (D_mem hN _).mp hmemi
  have hdj : (D N).getD (i+1) 0 ∣ N := (D_mem hN _).mp hmemj
  have hci := compl_get hN i hkm
  have hcj := compl_get hN (i+1) hi
  set A := (D N).getD i 0 with hA
  set B := (D N).getD (i+1) 0 with hB
  have hB0 : 0 < B := Nat.pos_of_dvd_of_pos hdj hN
  have hNB : 0 < N / B := Nat.div_pos (Nat.le_of_dvd hN hdj) hB0
  have hidx1 : (D N).length - 1 - i = (D N).length - 2 - i + 1 := by omega
  have hidx2 : (D N).length - 1 - (i + 1) = (D N).length - 2 - i := by omega
  rw [← hidx1, ← hidx2, ← hci, ← hcj]
  have h1 : 2 * A * (N / B) < B * (N / B) := (Nat.mul_lt_mul_right hNB).mpr (by omega)
  rw [Nat.mul_div_cancel' hdj] at h1
  have hNA : N = A * (N / A) := (Nat.mul_div_cancel' hdi).symm
  have h3 : A * (2 * (N / B)) = 2 * A * (N / B) := by ring
  have h2 : A * (2 * (N / B)) < A * (N / A) := by rw [h3]; omega
  exact Nat.lt_of_mul_lt_mul_left h2

/- ## Evenness of the jump count -/

theorem count_eq_card (hN : 0 < N) :
    ((D N).zip (D N).tail).countP (fun p => decide (p.2 > 2 * p.1))
      = (Finset.filter (fun i => (D N).getD (i+1) 0 > 2 * (D N).getD i 0)
          (Finset.range ((D N).length - 1))).card := by
  rw [zip_map_range, List.countP_map]
  have hfn : ((fun p : ℕ × ℕ => decide (p.2 > 2 * p.1)) ∘
        (fun i => ((D N).getD i 0, (D N).getD (i+1) 0)))
      = (fun i => decide ((D N).getD (i+1) 0 > 2 * (D N).getD i 0)) := by
    funext i; rfl
  rw [hfn, List.countP_eq_length_filter]
  have hnd : ((List.range ((D N).length - 1)).filter
      (fun i => decide ((D N).getD (i+1) 0 > 2 * (D N).getD i 0))).Nodup :=
    List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hnd]
  have hfe : (Finset.filter (fun i => (D N).getD (i+1) 0 > 2 * (D N).getD i 0)
        (Finset.range ((D N).length - 1)))
      = ((List.range ((D N).length - 1)).filter
          (fun i => decide ((D N).getD (i+1) 0 > 2 * (D N).getD i 0))).toFinset := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_filter, List.mem_toFinset,
      List.mem_range, decide_eq_true_iff]
  rw [← hfe]

theorem card_even (hN : 0 < N)
    (hfix : ∀ m, (D N).length = 2 * m → ¬ ((D N).getD m 0 > 2 * (D N).getD (m - 1) 0)) :
    2 ∣ (Finset.filter (fun i => (D N).getD (i+1) 0 > 2 * (D N).getD i 0)
          (Finset.range ((D N).length - 1))).card := by
  have hlen : 0 < (D N).length := D_len_pos hN
  set F : Finset ℕ := Finset.filter (fun i => (D N).getD (i+1) 0 > 2 * (D N).getD i 0)
      (Finset.range ((D N).length - 1)) with hFdef
  have hmemF : ∀ i ∈ F, i ∈ Finset.range ((D N).length - 1) ∧
      (D N).getD (i+1) 0 > 2 * (D N).getD i 0 := by
    intro i hi
    simpa [hFdef] using hi
  have hirF : ∀ i ∈ F, i < (D N).length - 1 := fun i hi =>
    Finset.mem_range.mp (hmemF i hi).1
  have hinv : ∀ i ∈ F, (D N).length - 2 - i ∈ F := by
    intro i hi
    have hir : i < (D N).length - 1 := Finset.mem_range.mp (hmemF i hi).1
    have hgi := good_inv hN i (by omega) (hmemF i hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hgi⟩
  rcases Nat.even_or_odd (D N).length with hev | hodd
  · obtain ⟨k, hk⟩ := hev
    have hm : (D N).length = 2 * k := by omega
    set m := k
    set F₁ : Finset ℕ := F.filter (fun i => i < m) with hF₁def
    have hF₁sub : F₁ ⊆ F := Finset.filter_subset _ _
    have key2 : F ⊆ F₁ ∪ Finset.image (fun i => (D N).length - 2 - i) F₁ := by
      intro i hi
      have hir := hirF i hi
      by_cases him : i < m
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, him⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(D N).length - 2 - i, Finset.mem_filter.mpr ⟨hinv i hi, by omega⟩, by omega⟩)
    have key3 : F₁ ∪ Finset.image (fun i => (D N).length - 2 - i) F₁ ⊆ F := by
      apply Finset.union_subset
      · exact fun a ha => hF₁sub ha
      · intro b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact hinv a (hF₁sub ha)
    have hdisj : Disjoint F₁ (Finset.image (fun i => (D N).length - 2 - i) F₁) := by
      rw [Finset.disjoint_right]
      intro j hj
      obtain ⟨i, hiF₁, hjeq⟩ := Finset.mem_image.mp hj
      have hi' : i ∈ F ∧ i < m := by simpa [hF₁def] using hiF₁
      have hir := hirF i hi'.1
      have hgg : (D N).getD (i+1) 0 > 2 * (D N).getD i 0 := (hmemF i hi'.1).2
      simp only [hF₁def, Finset.mem_filter]
      intro hcontra
      obtain ⟨-, hjm⟩ := hcontra
      rcases Nat.lt_or_ge j (m-1) with hjm' | hjm'
      · omega
      · have him1 : i = m - 1 := by omega
        have hmk : m - 1 + 1 = m := by omega
        rw [him1, hmk] at hgg
        exact hfix m hm hgg
    have hinj : Set.InjOn (fun i => (D N).length - 2 - i) ↑F₁ := by
      intro a ha b hb hab
      have ha' : a ∈ F ∧ a < m := by simpa [hF₁def] using ha
      have hb' : b ∈ F ∧ b < m := by simpa [hF₁def] using hb
      have har := hirF a ha'.1
      have hbr := hirF b hb'.1
      have hab' : (D N).length - 2 - a = (D N).length - 2 - b := hab
      omega
    have hcard2 : (Finset.image (fun i => (D N).length - 2 - i) F₁).card = F₁.card :=
      Finset.card_image_of_injOn hinj
    have hun : F = F₁ ∪ Finset.image (fun i => (D N).length - 2 - i) F₁ :=
      le_antisymm key2 key3
    rw [hun, Finset.card_union_of_disjoint hdisj, hcard2]
    exact ⟨F₁.card, by omega⟩
  · obtain ⟨k, hk⟩ := hodd
    have hm : (D N).length = 2 * k + 1 := by omega
    set m := k
    set F₁ : Finset ℕ := F.filter (fun i => i < m) with hF₁def
    have hF₁sub : F₁ ⊆ F := Finset.filter_subset _ _
    have key2 : F ⊆ F₁ ∪ Finset.image (fun i => (D N).length - 2 - i) F₁ := by
      intro i hi
      have hir := hirF i hi
      by_cases him : i < m
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, him⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(D N).length - 2 - i, Finset.mem_filter.mpr ⟨hinv i hi, by omega⟩, by omega⟩)
    have key3 : F₁ ∪ Finset.image (fun i => (D N).length - 2 - i) F₁ ⊆ F := by
      apply Finset.union_subset
      · exact fun a ha => hF₁sub ha
      · intro b hb
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        exact hinv a (hF₁sub ha)
    have hdisj : Disjoint F₁ (Finset.image (fun i => (D N).length - 2 - i) F₁) := by
      rw [Finset.disjoint_right]
      intro j hj
      obtain ⟨i, hiF₁, hjeq⟩ := Finset.mem_image.mp hj
      have hi' : i ∈ F ∧ i < m := by simpa [hF₁def] using hiF₁
      have hir := hirF i hi'.1
      simp only [hF₁def, Finset.mem_filter]
      intro hcontra
      obtain ⟨-, hjm⟩ := hcontra
      omega
    have hinj : Set.InjOn (fun i => (D N).length - 2 - i) ↑F₁ := by
      intro a ha b hb hab
      have ha' : a ∈ F ∧ a < m := by simpa [hF₁def] using ha
      have hb' : b ∈ F ∧ b < m := by simpa [hF₁def] using hb
      have har := hirF a ha'.1
      have hbr := hirF b hb'.1
      have hab' : (D N).length - 2 - a = (D N).length - 2 - b := hab
      omega
    have hcard2 : (Finset.image (fun i => (D N).length - 2 - i) F₁).card = F₁.card :=
      Finset.card_image_of_injOn hinj
    have hun : F = F₁ ∪ Finset.image (fun i => (D N).length - 2 - i) F₁ :=
      le_antisymm key2 key3
    rw [hun, Finset.card_union_of_disjoint hdisj, hcard2]
    exact ⟨F₁.card, by omega⟩

end Compl

/- ## Main theorem -/

theorem main (n : ℕ) (hn : 0 < n) : Odd (OeisA237271.a (n ^ 2)) := by
  have hN : 0 < n ^ 2 := by positivity
  have hfix : ∀ m, (D (n ^ 2)).length = 2 * m →
      ¬ ((D (n ^ 2)).getD m 0 > 2 * (D (n ^ 2)).getD (m - 1) 0) := by
    intro m hm hgg
    have hlen : 0 < (D (n ^ 2)).length := D_len_pos hN
    have hm1 : 0 < m := by omega
    have hlen1 : m - 1 < (D (n ^ 2)).length := by omega
    have hlen2 : m < (D (n ^ 2)).length := by omega
    have hdm : (D (n ^ 2)).getD (m-1) 0 ∈ D (n ^ 2) := getD_mem hlen1
    have hem : (D (n ^ 2)).getD m 0 ∈ D (n ^ 2) := getD_mem hlen2
    have hdd : (D (n ^ 2)).getD (m-1) 0 ∣ n ^ 2 := (D_mem hN _).mp hdm
    have hed : (D (n ^ 2)).getD m 0 ∣ n ^ 2 := (D_mem hN _).mp hem
    have hposd : 0 < (D (n ^ 2)).getD (m-1) 0 := Nat.pos_of_dvd_of_pos hdd hN
    have hp := D_pair (n ^ 2)
    rw [List.pairwise_iff_getElem] at hp
    have hne : (D (n ^ 2)).getD (m-1) 0 ≠ (D (n ^ 2)).getD m 0 := by
      have hnd := D_nodup (n ^ 2)
      rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hnd
      rw [List.getD_eq_getElem (D (n ^ 2)) 0 hlen1, List.getD_eq_getElem (D (n ^ 2)) 0 hlen2]
      exact hnd _ _ hlen1 hlen2 (by omega)
    have hle : (D (n ^ 2)).getD (m-1) 0 ≤ (D (n ^ 2)).getD m 0 := by
      rw [List.getD_eq_getElem (D (n ^ 2)) 0 hlen1, List.getD_eq_getElem (D (n ^ 2)) 0 hlen2]
      exact hp _ _ hlen1 hlen2 (by omega)
    have hlt : (D (n ^ 2)).getD (m-1) 0 < (D (n ^ 2)).getD m 0 := by omega
    have hcomp := compl_get hN m hlen2
    have hcomp' : n ^ 2 / (D (n ^ 2)).getD m 0 = (D (n ^ 2)).getD (m-1) 0 := by
      have hidx : (D (n ^ 2)).length - 1 - m = m - 1 := by omega
      rw [hidx] at hcomp
      exact hcomp
    have hdeN : (D (n ^ 2)).getD (m-1) 0 * (D (n ^ 2)).getD m 0 = n ^ 2 := by
      have h := Nat.mul_div_cancel' hed
      rw [hcomp'] at h
      exact (Nat.mul_comm _ _).trans h
    have hdeN2 : (D (n ^ 2)).getD m 0 * (D (n ^ 2)).getD (m-1) 0 = n ^ 2 :=
      (Nat.mul_comm _ _).trans hdeN
    have hnL : n ∈ D (n ^ 2) := (D_mem hN _).mpr ⟨n, by rw [Nat.pow_two]⟩
    have hn2 : n * n = n ^ 2 := by rw [Nat.pow_two]
    rcases Nat.lt_or_ge ((D (n ^ 2)).getD (m-1) 0) n with hdn | hdn
    · have hne2 : n < (D (n ^ 2)).getD m 0 := by
        have h1 : n * (D (n ^ 2)).getD (m-1) 0 < n * n := (Nat.mul_lt_mul_left hn).mpr hdn
        have h2 : n * (D (n ^ 2)).getD (m-1) 0
            < (D (n ^ 2)).getD m 0 * (D (n ^ 2)).getD (m-1) 0 := by omega
        exact Nat.lt_of_mul_lt_mul_right h2
      have hz : ((D (n ^ 2)).getD (m-1) 0, (D (n ^ 2)).getD m 0)
          ∈ (D (n ^ 2)).zip ((D (n ^ 2)).tail) := by
        rw [zip_map_range]
        have hkey : ((D (n ^ 2)).getD (m - 1) 0, (D (n ^ 2)).getD (m - 1 + 1) 0)
            = ((D (n ^ 2)).getD (m - 1) 0, (D (n ^ 2)).getD m 0) := by
          have hmk : m - 1 + 1 = m := by omega
          rw [hmk]
        have hmem : m - 1 ∈ List.range ((D (n ^ 2)).length - 1) :=
          List.mem_range.mpr (by omega)
        have hmz := List.mem_map_of_mem
          (f := fun i : ℕ => ((D (n ^ 2)).getD i 0, (D (n ^ 2)).getD (i+1) 0))
          (a := m - 1) hmem
        rw [hkey] at hmz
        exact hmz
      exact no_between (D (n ^ 2)) (D_pair (n ^ 2)) _ hz n hnL hdn hne2
    · have hNd : n ^ 2 / (D (n ^ 2)).getD (m-1) 0 = (D (n ^ 2)).getD m 0 := by
        have h1 := Nat.mul_div_cancel' hdd
        exact Nat.eq_of_mul_eq_mul_left hposd (h1.trans hdeN.symm)
      have hle2 : n ^ 2 / (D (n ^ 2)).getD (m-1) 0 ≤ n ^ 2 / n :=
        Nat.div_le_div_left hdn (by omega)
      have hnself : n ^ 2 / n = n := by rw [Nat.pow_two]; exact Nat.mul_div_cancel_left n hn
      omega
  have heven := card_even hN hfix
  refine Nat.odd_iff.mpr ?_
  rw [a_eq, count_eq_card hN]
  omega

end S237271D

theorem swarm_proof : ∀ (n : ℕ) (hn : 0 < n), Odd (OeisA237271.a (n ^ 2)) :=
  fun n hn => S237271D.main n hn
