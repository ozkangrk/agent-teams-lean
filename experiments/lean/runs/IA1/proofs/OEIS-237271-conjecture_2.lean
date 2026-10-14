import FormalConjectures.OEIS.«237271»

open OeisA237271

theorem swarm_proof (n : ℕ) : a n = num2DenseSublists n := by
  dsimp only [a, num2DenseSublists]
  have key : ∀ d d' (hp : (d, d') ∈ List.zip (n.divisors.sort (· ≤ ·))
      ((n.divisors.sort (· ≤ ·)).tail)),
      (Odd d' ∧ d' ≥ 2 * d) ↔ 2 * d < d' := by
    intro d d' hp
    set L : List ℕ := n.divisors.sort (· ≤ ·) with hLdef
    have hS : L.SortedLE := (Finset.pairwise_sort _ _).sortedLE
    obtain ⟨i, hi, hz⟩ := List.mem_iff_getElem.mp hp
    rw [List.getElem_zip] at hz
    have hzl : (L.zip L.tail).length = L.tail.length := by
      rw [List.length_zip, List.length_tail]
      exact Nat.min_eq_right (Nat.sub_le _ _)
    have htail : i < L.tail.length := by rw [← hzl]; exact hi
    have hi1 : i + 1 < L.length := by
      rw [List.length_tail] at htail; omega
    rw [List.getElem_tail htail] at hz
    rw [Prod.mk.injEq] at hz
    obtain ⟨hd, hd'⟩ := hz
    have hdL : d' ∈ L := by rw [← hd']; exact List.getElem_mem hi1
    obtain ⟨hddvd, hdne⟩ := Nat.mem_divisors.mp ((Finset.mem_sort (· ≤ ·)).mp hdL)
    have hnoBetween : ∀ e ∈ L, d < e → e < d' → False := by
      intro e he h1 h2
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
      rcases Nat.lt_or_ge j (i + 1) with hjlt | hjge
      · have hle : L[j] ≤ L[i] := hS.getElem_le_getElem_of_le (by omega)
        omega
      · have hle : L[i + 1] ≤ L[j] := hS.getElem_le_getElem_of_le (by omega)
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
        have hd2 : 2 * t ∣ n := Nat.dvd_trans (⟨1, by omega⟩ : 2 * t ∣ d') hddvd
        have htdvd : t ∣ n := Nat.dvd_trans (⟨2, by omega⟩ : t ∣ 2 * t) hd2
        have htL : t ∈ L :=
          (Finset.mem_sort (· ≤ ·)).mpr (Nat.mem_divisors.mpr ⟨htdvd, by omega⟩)
        exact hnoBetween t htL (by omega) (by rw [ht2]; omega)
      · exact hO
  congr 1
  refine List.countP_congr fun x hx => ?_
  obtain ⟨d, d'⟩ := x
  by_cases hlt : 2 * d < d'
  · have h2 := (key d d' hx).mpr hlt
    simp [h2, hlt]
  · have h2 : ¬ (Odd d' ∧ d' ≥ 2 * d) := fun hc => hlt ((key d d' hx).mp hc)
    simp [h2, hlt]
